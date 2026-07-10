use std::iter::Peekable;

use crate::ast::literal::{LitKind, LitVal, StrPrefix};
use crate::ast::nodes::InitializerList;
use crate::ast::{self, NameId};
use crate::ast::{Designator, NodeKind, NodeRef};
use crate::codegen::mir_gen::MirGen;
use crate::mir::{ConstValueId, ConstValueKind, MirArrayLayout, MirType, Operand, Place, Rvalue, TypeId};
use crate::semantic::literal_utils::lower_string_literal;
use crate::semantic::{ArraySizeType, FieldLayout, QualType, RecordMember, TypeKind, TypeRef};

struct ArrayInitArgs {
    element_qt: QualType,
    size: usize,
    target_ty: QualType,
    destination: Option<Place>,
    is_top_level: bool,
    existing_op: Option<Operand>,
}

impl<'a> MirGen<'a> {
    fn visit_init_list(&mut self, list: &InitializerList, target_ty: QualType, destination: Option<Place>) -> Operand {
        let range = list.init_start.range(list.init_len);
        let mut iter = range.peekable();
        let fields = self.visit_struct_fields_recursive(&mut iter, None, &[], target_ty, None);
        self.finalize_struct_init(fields, target_ty, destination)
    }

    fn get_flattened_type_info(&self, ty: TypeRef) -> (Vec<RecordMember>, Vec<FieldLayout>) {
        let mut members = Vec::new();
        let mut offsets = Vec::new();
        let ty = self.registry.get(ty);
        ty.flatten_members_with_layouts(self.registry, &mut members, &mut offsets, 0);
        (members, offsets)
    }

    fn visit_struct_fields_recursive(
        &mut self,
        iter: &mut Peekable<impl Iterator<Item = NodeRef>>,
        pending: Option<(NodeRef, Option<(NodeRef, u16)>)>,
        pending_path: &[usize],
        target_qt: QualType,
        existing_op: Option<Operand>,
    ) -> Vec<(usize, Operand)> {
        let type_info = self.registry.get(target_qt.ty());
        let (members, is_union) = match &type_info.kind {
            TypeKind::Record { members, is_union, .. } => (members.clone(), *is_union),
            _ => return Vec::new(),
        };

        let mut hierarchical_offsets = Vec::with_capacity(members.len());
        let mut offset = 0;
        for m in members.iter() {
            hierarchical_offsets.push(offset);
            offset += self.count_flattened_members(m);
        }

        let mut field_operands = Vec::new();
        let mut current_pos = 0;
        let mut first_item_processed = false;

        loop {
            let (initializer, designator, is_pending) =
                if let (Some((init, desig)), false) = (pending, first_item_processed) {
                    first_item_processed = true;
                    (init, desig, true)
                } else if let Some(&item) = iter.peek() {
                    let NodeKind::InitializerItem(init) = self.ast.get_kind(item) else {
                        iter.next();
                        continue;
                    };
                    (
                        init.initializer,
                        (init.designator_len > 0).then_some((init.designator_start, init.designator_len)),
                        false,
                    )
                } else {
                    break;
                };

            let Some((field_idx, active_path)) =
                self.resolve_init_field_target(&members, current_pos, designator, pending_path, is_pending)
            else {
                break;
            };

            if field_idx >= members.len() {
                break;
            }

            if !is_pending {
                iter.next();
            }

            let m = &members[field_idx];
            let flat_base = hierarchical_offsets[field_idx];
            let value = self.visit_nested_aggregate_init(
                iter,
                initializer,
                designator,
                active_path,
                m,
                field_idx,
                existing_op.clone(),
            );

            for (sub_idx, op) in value {
                field_operands.push((flat_base + sub_idx, op));
            }

            current_pos = if is_union { members.len() } else { field_idx + 1 };
        }
        field_operands
    }

    fn resolve_init_field_target(
        &self,
        members: &[RecordMember],
        current_pos: usize,
        designator: Option<(NodeRef, u16)>,
        pending_path: &[usize],
        is_pending: bool,
    ) -> Option<(usize, Vec<usize>)> {
        if is_pending && !pending_path.is_empty() {
            return Some((pending_path[0], pending_path[1..].to_vec()));
        }

        match designator {
            Some((d_start, _)) => {
                if let NodeKind::Designator(Designator::FieldName(name)) = self.ast.get_kind(d_start) {
                    self.find_member(members, *name)
                } else {
                    if is_pending {
                        panic!("Array designator in struct initializer");
                    }
                    None
                }
            }
            None => {
                let mut pos = current_pos;
                while pos < members.len() && members[pos].name.is_none() && members[pos].bit_field_size.is_some() {
                    pos += 1;
                }
                Some((pos, Vec::new()))
            }
        }
    }

    fn visit_nested_aggregate_init(
        &mut self,
        iter: &mut Peekable<impl Iterator<Item = NodeRef>>,
        initializer: NodeRef,
        designator: Option<(NodeRef, u16)>,
        active_path: Vec<usize>,
        m: &RecordMember,
        field_idx: usize,
        existing_op: Option<Operand>,
    ) -> Vec<(usize, Operand)> {
        let recursion_args = if !active_path.is_empty() || (designator.is_some() && designator.unwrap().1 > 1) {
            let (next_pending, next_path) = if !active_path.is_empty() {
                (Some((initializer, designator)), active_path)
            } else {
                let (d_start, d_len) = designator.unwrap();
                (
                    Some((initializer, Some((d_start.add_offset(1), d_len - 1)))),
                    Vec::new(),
                )
            };
            Some((next_pending, next_path))
        } else if self.should_recurse_aggregate(m.member_type, initializer) {
            Some((Some((initializer, None)), Vec::new()))
        } else {
            None
        };

        if let Some((next_pending, next_path)) = recursion_args {
            let sub_existing = self.get_existing_struct_field(&existing_op, field_idx);
            match &self.registry.get(m.member_type.ty()).kind {
                TypeKind::Record { .. } => {
                    let fields =
                        self.visit_struct_fields_recursive(iter, next_pending, &next_path, m.member_type, sub_existing);
                    if m.name.is_none() {
                        fields
                    } else {
                        vec![(0, self.finalize_struct_init(fields, m.member_type, None))]
                    }
                }
                TypeKind::Array { element_type, size } => {
                    let array_size = if let ArraySizeType::Constant(s) = size { *s } else { 0 };
                    let op = self.visit_array_init_from_iter(
                        iter,
                        next_pending,
                        ArrayInitArgs {
                            element_qt: QualType::unqualified(*element_type),
                            size: array_size,
                            target_ty: m.member_type,
                            destination: None,
                            is_top_level: false,
                            existing_op: sub_existing,
                        },
                    );
                    vec![(0, op)]
                }
                _ => unreachable!("Designator path on non-aggregate"),
            }
        } else if let NodeKind::InitializerList(list) = self.ast.get_kind(initializer)
            && m.name.is_none()
            && m.member_type.is_record()
        {
            let range = list.init_start.range(list.init_len);
            let mut sub_iter = range.peekable();
            let sub_existing = self.get_existing_struct_field(&existing_op, field_idx);
            self.visit_struct_fields_recursive(&mut sub_iter, None, &[], m.member_type, sub_existing)
        } else {
            vec![(0, self.visit_init(initializer, m.member_type, None))]
        }
    }

    fn should_recurse_aggregate(&self, target_qt: QualType, initializer: NodeRef) -> bool {
        let kind = &self.registry.get(target_qt.ty()).kind;
        if !matches!(kind, TypeKind::Record { .. } | TypeKind::Array { .. }) {
            return false;
        }

        let init_kind = self.ast.get_kind(initializer);
        if matches!(init_kind, NodeKind::InitializerList(_)) {
            return false;
        }

        if let NodeKind::Literal(lit) = init_kind
            && lit.kind() == LitKind::String
            && let TypeKind::Array { element_type, .. } = kind
            && self.registry.is_char_type(*element_type)
        {
            return false;
        }

        let is_compatible = self
            .registry
            .is_compatible(self.ast.qual_type_of(initializer).strip_all(), target_qt.strip_all());

        !is_compatible
    }

    fn resolve_designator_range(&mut self, designator: NodeRef) -> (usize, usize) {
        match self.ast.get_kind(designator) {
            NodeKind::Designator(Designator::ArrayIndex(idx_expr)) => {
                let idx = self.evaluate_constant_usize(*idx_expr, "Array designator must be constant");
                (idx, idx)
            }
            NodeKind::Designator(Designator::ArrayRange(start, end)) => {
                let s = self.evaluate_constant_usize(*start, "Range start must be constant");
                let e = self.evaluate_constant_usize(*end, "Range end must be constant");
                if e < s {
                    panic!("Array range end < start");
                }
                (s, e)
            }
            _ => panic!("Invalid designator for array"),
        }
    }

    fn visit_array_init(
        &mut self,
        list: &ast::nodes::InitializerList,
        element_ty: QualType,
        size: usize,
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        let range = list.init_start.range(list.init_len);
        let mut iter = range.peekable();
        self.visit_array_init_from_iter(
            &mut iter,
            None,
            ArrayInitArgs {
                element_qt: element_ty,
                size,
                target_ty,
                destination,
                is_top_level: true,
                existing_op: None,
            },
        )
    }

    fn visit_array_init_from_iter(
        &mut self,
        iter: &mut Peekable<impl Iterator<Item = NodeRef>>,
        pending: Option<(NodeRef, Option<(NodeRef, u16)>)>,
        args: ArrayInitArgs,
    ) -> Operand {
        let ArrayInitArgs {
            element_qt,
            size,
            target_ty,
            destination,
            is_top_level,
            existing_op,
        } = args;
        let mut elements: Vec<Option<Operand>> = self.get_existing_array_elements(&existing_op, size);
        let mut current_idx = 0;
        let mut first_item_processed = false;

        loop {
            let (initializer, designator, is_pending) =
                if let (Some((init, desig)), false) = (pending, first_item_processed) {
                    first_item_processed = true;
                    (init, desig, true)
                } else if let Some(&item) = iter.peek() {
                    let NodeKind::InitializerItem(init) = self.ast.get_kind(item) else {
                        iter.next();
                        continue;
                    };
                    (
                        init.initializer,
                        (init.designator_len > 0).then_some((init.designator_start, init.designator_len)),
                        false,
                    )
                } else {
                    break;
                };

            if !is_top_level && !is_pending && designator.is_some() {
                break;
            }

            if designator.is_none() && size > 0 && current_idx >= size {
                break;
            }

            let Some((start, end)) = self.resolve_array_init_range(current_idx, designator, is_pending) else {
                break;
            };

            if !is_pending {
                iter.next();
            }

            let existing_el = if start < elements.len() {
                elements[start].clone()
            } else {
                None
            };
            let operand = self.visit_array_element_init(iter, initializer, designator, element_qt, existing_el);

            if end >= elements.len() {
                elements.resize(end + 1, None);
            }
            for item in elements.iter_mut().take(end + 1).skip(start) {
                *item = Some(match item.take() {
                    Some(existing_op) => self.merge_operands(existing_op, operand.clone(), element_qt),
                    None => operand.clone(),
                });
            }
            current_idx = end + 1;
        }

        let mir_elem_ty = self.lower_qual_type(element_qt);
        let final_elements = elements
            .into_iter()
            .map(|op| op.unwrap_or_else(|| Operand::Constant(self.create_constant(mir_elem_ty, ConstValueKind::Zero))))
            .collect();

        self.finalize_array_init(final_elements, target_ty, destination)
    }

    fn resolve_array_init_range(
        &mut self,
        current_idx: usize,
        designator: Option<(NodeRef, u16)>,
        is_pending: bool,
    ) -> Option<(usize, usize)> {
        let Some((d_start, _)) = designator else {
            return Some((current_idx, current_idx));
        };

        match self.ast.get_kind(d_start) {
            NodeKind::Designator(Designator::ArrayIndex(_) | Designator::ArrayRange(_, _)) => {
                Some(self.resolve_designator_range(d_start))
            }
            _ => {
                if is_pending {
                    panic!("Field designator in array initializer");
                }
                None
            }
        }
    }

    fn visit_array_element_init(
        &mut self,
        iter: &mut Peekable<impl Iterator<Item = NodeRef>>,
        initializer: NodeRef,
        designator: Option<(NodeRef, u16)>,
        element_qt: QualType,
        existing_op: Option<Operand>,
    ) -> Operand {
        let next_pending = if let Some((d_start, d_len)) = designator
            && d_len > 1
        {
            let next_d_start = d_start.add_offset(1);
            let next_d_len = d_len - 1;
            Some((initializer, Some((next_d_start, next_d_len))))
        } else if self.should_recurse_aggregate(element_qt, initializer) {
            Some((initializer, None))
        } else {
            None
        };

        if let Some(pending) = next_pending {
            match &self.registry.get(element_qt.ty()).kind {
                TypeKind::Record { .. } => {
                    let fields = self.visit_struct_fields_recursive(iter, Some(pending), &[], element_qt, existing_op);
                    self.finalize_struct_init(fields, element_qt, None)
                }
                TypeKind::Array { element_type, size } => {
                    let array_size = if let ArraySizeType::Constant(s) = size { *s } else { 0 };
                    self.visit_array_init_from_iter(
                        iter,
                        Some(pending),
                        ArrayInitArgs {
                            element_qt: QualType::unqualified(*element_type),
                            size: array_size,
                            target_ty: element_qt,
                            destination: None,
                            is_top_level: false,
                            existing_op,
                        },
                    )
                }
                _ => unreachable!("Designator path on non-aggregate"),
            }
        } else {
            self.visit_init(initializer, element_qt, None)
        }
    }

    fn finalize_initializer_generic<T, C, R>(
        &mut self,
        target_ty: QualType,
        data: T,
        create_const: C,
        create_rvalue: R,
        destination: Option<Place>,
    ) -> Operand
    where
        C: FnOnce(&mut Self, T) -> ConstValueKind,
        R: FnOnce(T) -> Rvalue,
    {
        let mir_ty = self.lower_qual_type(target_ty);
        if self.func_state.is_none() {
            let const_kind = create_const(self, data);
            Operand::Constant(self.create_constant(mir_ty, const_kind))
        } else if let Some(place) = destination {
            let rval = create_rvalue(data);
            self.add_stmt(crate::mir::MirStmt::Assign(place.clone(), rval));
            Operand::Copy(Box::new(place))
        } else {
            let rval = create_rvalue(data);
            self.emit_rvalue_to_operand(rval, mir_ty)
        }
    }

    fn finalize_struct_init(
        &mut self,
        field_operands: Vec<(usize, Operand)>,
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        let fields_types: Vec<QualType> = match &self.registry.get(target_ty.ty()).kind {
            TypeKind::Record { members, .. } => members.iter().map(|m| m.member_type).collect(),
            _ => Vec::new(),
        };

        // Dedup by index, merging if existing
        let mut final_fields: Vec<(usize, Operand)> = Vec::new();
        for (idx, op) in field_operands {
            if let Some(existing) = final_fields.iter_mut().find(|(i, _)| *i == idx) {
                let field_ty = fields_types[idx];
                existing.1 = self.merge_operands(existing.1.clone(), op, field_ty);
            } else {
                final_fields.push((idx, op));
            }
        }
        final_fields.sort_by_key(|(idx, _)| *idx);

        self.finalize_initializer_generic(
            target_ty,
            final_fields,
            |this, fields| {
                let const_fields = fields
                    .into_iter()
                    .map(|(idx, op)| (idx, this.operand_to_const_id_strict(op, "Global struct init error")))
                    .collect();
                ConstValueKind::StructLiteral(const_fields)
            },
            Rvalue::StructLiteral,
            destination,
        )
    }

    fn finalize_array_init(
        &mut self,
        elements: Vec<Operand>,
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        self.finalize_initializer_generic(
            target_ty,
            elements,
            |this, elems| {
                let const_elements = elems
                    .into_iter()
                    .map(|op| this.operand_to_const_id_strict(op, "Global array init error"))
                    .collect();
                ConstValueKind::ArrayLiteral(const_elements)
            },
            Rvalue::ArrayLiteral,
            destination,
        )
    }

    pub(crate) fn visit_init(&mut self, init: NodeRef, target_qt: QualType, destination: Option<Place>) -> Operand {
        let kind = self.ast.get_kind(init);

        if let NodeKind::InitializerList(list) = kind {
            return self.visit_list_init(list, target_qt, destination);
        }

        if let NodeKind::Literal(lit) = kind
            && lit.kind() == LitKind::String
        {
            let array_info = if let TypeKind::Array { element_type, size } = &self.registry.get(target_qt.ty()).kind {
                Some((*element_type, *size))
            } else {
                None
            };

            if let Some((element_type, size)) = array_info {
                return self.visit_string_array_init(init, element_type, &size);
            }
        }

        let operand = self.visit_expression(init, true);
        let mir_target_ty = self.lower_qual_type(target_qt);
        let conv_op = self.apply_conversions(operand.clone(), init, mir_target_ty);

        if self.get_operand_type(&conv_op) == mir_target_ty {
            conv_op
        } else {
            // Brace elision: scalar -> aggregate
            self.visit_brace_elision(operand, init, target_qt, destination)
        }
    }

    fn visit_string_array_init(&mut self, lit_node: NodeRef, element_type: TypeRef, size: &ArraySizeType) -> Operand {
        let NodeKind::Literal(lit) = self.ast.get_kind(lit_node) else {
            unreachable!()
        };
        lit.with_val(|val| {
            let (val, prefix) = if let LitVal::String { value, prefix } = val {
                (value, prefix)
            } else {
                unreachable!()
            };
            let fixed_size = if let ArraySizeType::Constant(s) = size {
                Some(*s)
            } else {
                None
            };
            Operand::Constant(self.create_array_const_from_string(
                val,
                *prefix,
                fixed_size,
                Some(QualType::unqualified(element_type)),
            ))
        })
    }

    fn visit_list_init(&mut self, list: &InitializerList, target_qt: QualType, destination: Option<Place>) -> Operand {
        let (is_record, array_info) = {
            let target_type = self.registry.get(target_qt.ty());
            match &target_type.kind {
                TypeKind::Record { .. } | TypeKind::Complex { .. } => (true, None),
                TypeKind::Array { element_type, size } => (false, Some((*element_type, *size))),
                _ => (false, None),
            }
        };

        if is_record {
            return self.visit_init_list(list, target_qt, destination);
        }

        if let Some((element_type, size)) = array_info {
            if list.init_len == 1 && self.registry.is_char_type(element_type) {
                let NodeKind::InitializerItem(item) = self.ast.get_kind(list.init_start) else {
                    unreachable!()
                };
                if let NodeKind::Literal(lit) = self.ast.get_kind(item.initializer)
                    && lit.kind() == LitKind::String
                {
                    return self.visit_string_array_init(item.initializer, element_type, &size);
                }
            }

            let array_size = if let ArraySizeType::Constant(s) = size { s } else { 0 };
            return self.visit_array_init(
                list,
                QualType::unqualified(element_type),
                array_size,
                target_qt,
                destination,
            );
        }

        // Scalar initialized with braces: { x } or {}
        if list.init_len == 0 {
            let mir_ty = self.lower_qual_type(target_qt);
            Operand::Constant(self.create_constant(mir_ty, ConstValueKind::Zero))
        } else {
            let NodeKind::InitializerItem(item) = self.ast.get_kind(list.init_start) else {
                unreachable!()
            };
            self.visit_init(item.initializer, target_qt, destination)
        }
    }

    fn create_array_const_from_string(
        &mut self,
        content: &str,
        prefix: StrPrefix,
        fixed_size: Option<usize>,
        elem_ty: Option<QualType>,
    ) -> crate::mir::ConstValueId {
        let parsed = lower_string_literal(content, prefix);
        let size = fixed_size.unwrap_or(parsed.size);

        let (mir_elem_ty, layout) = if let Some(qt) = elem_ty {
            let mir_elem_ty = self.lower_qual_type(qt);
            let _ = self.registry.ensure_layout(qt.ty());
            (mir_elem_ty, self.registry.get_layout(qt.ty()).into_owned())
        } else {
            let ty = self.registry.get_builtin_type(parsed.builtin_type);
            let mir_elem_ty = self.lower_qual_type(QualType::unqualified(ty));
            let _ = self.registry.ensure_layout(ty);
            (mir_elem_ty, self.registry.get_layout(ty).into_owned())
        };

        let constants = (0..size)
            .map(|i| {
                let v = parsed.values.get(i).cloned().unwrap_or(0);
                self.create_constant(mir_elem_ty, ConstValueKind::Int(v))
            })
            .collect();

        let array_ty = self.mb.add_type(MirType::Array {
            element: mir_elem_ty,
            size,
            layout: MirArrayLayout {
                size: 0,
                align: layout.alignment,
                stride: layout.size,
            },
        });

        self.create_constant(array_ty, ConstValueKind::ArrayLiteral(constants))
    }

    pub(super) fn visit_literal_string(&mut self, content: String, prefix: StrPrefix, qt: QualType) -> Operand {
        let mir_ty = self.lower_qual_type(qt);
        let elem_ty = self
            .registry
            .get(qt.ty())
            .get_array_element()
            .unwrap_or(self.registry.type_char);

        let array_const =
            self.create_array_const_from_string(&content, prefix, None, Some(QualType::unqualified(elem_ty)));
        let global_id = self.create_anon_global(mir_ty, array_const);

        Operand::Constant(self.create_constant(mir_ty, ConstValueKind::GlobalAddress(global_id, 0)))
    }

    pub(super) fn visit_compound_literal(&mut self, ty: QualType, init: NodeRef) -> Operand {
        let mir_ty = self.lower_qual_type(ty);

        if self.func_state.is_none() {
            let init_const = self
                .eval_init_to_const(init, ty)
                .expect("Global compound literal init must be const");

            let global_id = self.create_anon_global(mir_ty, init_const);

            Operand::Copy(Box::new(Place::Global(global_id)))
        } else {
            let (_, place) = self.create_temp_local(mir_ty);
            self.visit_init(init, ty, Some(place.clone()));
            Operand::Copy(Box::new(place))
        }
    }

    pub(super) fn eval_init_to_const(&mut self, init: NodeRef, ty: QualType) -> Option<crate::mir::ConstValueId> {
        let operand = self.visit_init(init, ty, None);
        self.operand_to_const_id(&operand)
    }

    fn visit_brace_elision(
        &mut self,
        operand: Operand,
        init: NodeRef,
        target_qt: QualType,
        destination: Option<Place>,
    ) -> Operand {
        let target_type = self.registry.get(target_qt.ty()).into_owned();
        match &target_type.kind {
            TypeKind::Array { element_type, size } => {
                let elem_ty = QualType::unqualified(*element_type);
                let final_op = self.visit_brace_elision(operand, init, elem_ty, None);
                let mir_elem_ty = self.lower_qual_type(elem_ty);
                let len = if let ArraySizeType::Constant(l) = size { *l } else { 1 };
                let mut elements = vec![final_op];
                while elements.len() < len {
                    elements.push(Operand::Constant(
                        self.create_constant(mir_elem_ty, ConstValueKind::Zero),
                    ));
                }
                self.finalize_array_init(elements, target_qt, destination)
            }
            TypeKind::Record { members, .. } if !members.is_empty() => {
                let (flat_members, _) = self.get_flattened_type_info(target_qt.ty());
                if flat_members.is_empty() {
                    let mir_target_ty = self.lower_qual_type(target_qt);
                    return Operand::Constant(self.create_constant(mir_target_ty, ConstValueKind::Zero));
                }
                let member_ty = flat_members[0].member_type;
                let final_op = self.visit_brace_elision(operand, init, member_ty, None);
                self.finalize_struct_init(vec![(0, final_op)], target_qt, destination)
            }
            _ => {
                let mir_target_ty = self.lower_qual_type(target_qt);
                let conv_op = self.apply_conversions(operand, init, mir_target_ty);
                if self.get_operand_type(&conv_op) != mir_target_ty {
                    Operand::Cast(mir_target_ty, Box::new(conv_op))
                } else {
                    conv_op
                }
            }
        }
    }

    fn count_flattened_members(&self, m: &RecordMember) -> usize {
        if m.name.is_some() {
            return 1;
        }
        if m.bit_field_size.is_some() {
            return 0;
        }
        let ty = m.member_type.ty();
        if !ty.is_record() {
            return 1;
        }
        let mut flat_members = Vec::new();
        let mut flat_offsets = Vec::new();
        let type_obj = self.registry.get(ty);
        type_obj.flatten_members_with_layouts(self.registry, &mut flat_members, &mut flat_offsets, 0);
        flat_members.len()
    }

    fn find_member(&self, members: &[RecordMember], name: NameId) -> Option<(usize, Vec<usize>)> {
        for (i, m) in members.iter().enumerate() {
            if m.name == Some(name) {
                return Some((i, Vec::new()));
            }
            if m.name.is_none()
                && let TypeKind::Record {
                    members: sub_members, ..
                } = &self.registry.get(m.member_type.ty()).kind
                && let Some((sub_idx, mut path)) = self.find_member(sub_members, name)
            {
                path.insert(0, sub_idx);
                return Some((i, path));
            }
        }
        None
    }

    fn merge_operands(&mut self, existing: Operand, new: Operand, ty: QualType) -> Operand {
        match (existing, new) {
            (Operand::Constant(existing_id), Operand::Constant(new_id)) => {
                let mir_ty = self.lower_qual_type(ty);
                let merged_id = self.merge_constants(existing_id, new_id, mir_ty);
                Operand::Constant(merged_id)
            }
            (_, new) => new,
        }
    }

    fn merge_constants(&mut self, existing_id: ConstValueId, new_id: ConstValueId, mir_ty: TypeId) -> ConstValueId {
        let existing_val = self.mb.get_constant(existing_id).clone();
        let new_val = self.mb.get_constant(new_id).clone();

        match (&existing_val.kind, &new_val.kind) {
            (ConstValueKind::Zero, _) => new_id,
            (ConstValueKind::StructLiteral(existing_fields), ConstValueKind::StructLiteral(new_fields)) => {
                let mut merged_fields = existing_fields.clone();
                for &(new_idx, new_field_const_id) in new_fields {
                    let field_ty = match self.mb.get_type(mir_ty) {
                        MirType::Record { field_types, .. } => field_types[new_idx],
                        _ => panic!("Expected Record type in merge_constants"),
                    };

                    if let Some(existing_field) = merged_fields.iter_mut().find(|(idx, _)| *idx == new_idx) {
                        existing_field.1 = self.merge_constants(existing_field.1, new_field_const_id, field_ty);
                    } else {
                        merged_fields.push((new_idx, new_field_const_id));
                    }
                }
                merged_fields.sort_by_key(|(idx, _)| *idx);
                self.create_constant(mir_ty, ConstValueKind::StructLiteral(merged_fields))
            }
            (ConstValueKind::ArrayLiteral(existing_elements), ConstValueKind::ArrayLiteral(new_elements)) => {
                let mut merged_elements = existing_elements.clone();
                let elem_ty = match self.mb.get_type(mir_ty) {
                    &MirType::Array { element, .. } => element,
                    _ => panic!("Expected Array type in merge_constants"),
                };

                for (idx, &new_el_id) in new_elements.iter().enumerate() {
                    let existing_el_id = merged_elements[idx];
                    merged_elements[idx] = self.merge_constants(existing_el_id, new_el_id, elem_ty);
                }
                self.create_constant(mir_ty, ConstValueKind::ArrayLiteral(merged_elements))
            }
            _ => new_id,
        }
    }

    fn get_existing_struct_field(&self, existing_op: &Option<Operand>, field_idx: usize) -> Option<Operand> {
        if let Some(Operand::Constant(const_id)) = existing_op {
            let const_val = self.mb.get_constant(*const_id);
            if let ConstValueKind::StructLiteral(fields) = &const_val.kind
                && let Some((_, field_const_id)) = fields.iter().find(|(idx, _)| *idx == field_idx)
            {
                return Some(Operand::Constant(*field_const_id));
            }
        }
        None
    }

    fn get_existing_array_elements(&self, existing_op: &Option<Operand>, size: usize) -> Vec<Option<Operand>> {
        if let Some(Operand::Constant(const_id)) = existing_op {
            let const_val = self.mb.get_constant(*const_id);
            if let ConstValueKind::ArrayLiteral(elements) = &const_val.kind {
                return elements.iter().map(|&el_id| Some(Operand::Constant(el_id))).collect();
            }
        }
        vec![None; size]
    }
}
