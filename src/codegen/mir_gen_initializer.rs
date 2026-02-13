use std::iter::Peekable;

use crate::ast;
use crate::ast::{Designator, NodeKind, NodeRef, literal};
use crate::codegen::mir_gen::MirGen;
use crate::mir::{ConstValueKind, MirArrayLayout, MirType, Operand, Place, Rvalue};
use crate::semantic::{ArraySizeType, QualType, StructMember, TypeKind};

impl<'a> MirGen<'a> {
    fn emit_initializer_list(
        &mut self,
        list_data: &ast::nodes::InitializerListData,
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        let range = list_data.init_start.range(list_data.init_len);
        let mut iter = range.peekable();
        let fields = self.emit_struct_fields_recursive(&mut iter, None, target_ty);
        self.finalize_struct_initializer(fields, target_ty, destination)
    }

    fn get_flattened_type_info(&self, ty_ref: crate::semantic::TypeRef) -> (Vec<StructMember>, Vec<u16>) {
        let mut members = Vec::new();
        let mut offsets = Vec::new();
        let ty = self.registry.get(ty_ref);
        ty.flatten_members_with_layouts(self.registry, &mut members, &mut offsets, 0);
        (members, offsets)
    }

    fn emit_struct_fields_recursive(
        &mut self,
        iter: &mut Peekable<impl Iterator<Item = NodeRef>>,
        pending_initializer: Option<NodeRef>,
        target_ty: QualType,
    ) -> Vec<(usize, Operand)> {
        let TypeKind::Record { members, .. } = &self.registry.get(target_ty.ty()).kind else {
            return Vec::new();
        };
        let is_union = self.registry.get(target_ty.ty()).is_union();
        let members = members.clone();

        // Precalculate flattened offsets for hierarchical members
        let mut hierarchical_offsets = Vec::with_capacity(members.len());
        let mut offset = 0;
        for m in &members {
            hierarchical_offsets.push(offset);
            if !is_union {
                offset += self.count_flattened_members(m);
            }
        }

        let mut field_operands = Vec::new();
        let mut current_pos = 0;
        let mut first_item_processed = false;

        loop {
            let (item_ref, is_pending) = if let Some(pending) = pending_initializer
                && !first_item_processed
            {
                first_item_processed = true;
                (pending, true)
            } else if let Some(r) = iter.peek() {
                (*r, false)
            } else {
                break;
            };

            let (initializer, designator) = match (is_pending, self.ast.get_kind(item_ref)) {
                (true, _) => (item_ref, None),
                (false, NodeKind::InitializerItem(init)) => (
                    init.initializer,
                    (init.designator_len > 0).then_some((init.designator_start, init.designator_len)),
                ),
                _ => {
                    iter.next();
                    continue;
                }
            };

            let (field_idx, nested_path) = match designator {
                Some((d_start, _)) => {
                    if let NodeKind::Designator(Designator::FieldName(name)) = self.ast.get_kind(d_start) {
                        if let Some(res) = self.find_member_recursive(&members, *name) {
                            res
                        } else {
                            break;
                        }
                    } else {
                        if is_pending {
                            panic!("Array designator in struct initializer");
                        }
                        break;
                    }
                }
                None => (current_pos, Vec::new()),
            };

            if field_idx >= members.len() {
                break;
            }

            if !is_pending {
                iter.next();
            }

            let m = &members[field_idx];
            let flat_base = hierarchical_offsets[field_idx];

            let value = if !nested_path.is_empty() || designator.is_some_and(|(_, len)| len > 1) {
                let (d_start, d_len) = designator.unwrap_or((NodeRef::ROOT, 0));
                let mut extra_iter = (d_len > 1).then(|| d_start.range(d_len).skip(1));
                self.emit_initializer_with_path_recursive(
                    &nested_path,
                    extra_iter.as_mut().map(|i| i as &mut dyn Iterator<Item = NodeRef>),
                    initializer,
                    m.member_type,
                )
            } else if self.should_recurse_aggregate(m.member_type, initializer) {
                match &self.registry.get(m.member_type.ty()).kind {
                    TypeKind::Record { .. } => {
                        let fields = self.emit_struct_fields_recursive(iter, Some(initializer), m.member_type);
                        if m.name.is_none() {
                            fields
                        } else {
                            vec![(0, self.finalize_struct_initializer(fields, m.member_type, None))]
                        }
                    }
                    TypeKind::Array { element_type, size } => {
                        let array_size = if let ArraySizeType::Constant(s) = size { *s } else { 0 };
                        let op = self.emit_array_initializer_from_iter(
                            iter,
                            Some(initializer),
                            QualType::unqualified(*element_type),
                            array_size,
                            m.member_type,
                            None,
                        );
                        vec![(0, op)]
                    }
                    _ => unreachable!(),
                }
            } else if matches!(self.ast.get_kind(initializer), NodeKind::InitializerList(_))
                && m.name.is_none()
                && m.member_type.ty().is_record()
            {
                // Anonymous member initialized with braces
                let NodeKind::InitializerList(list) = self.ast.get_kind(initializer) else {
                    unreachable!()
                };
                let range = list.init_start.range(list.init_len);
                let mut sub_iter = range.peekable();
                self.emit_struct_fields_recursive(&mut sub_iter, None, m.member_type)
            } else {
                vec![(0, self.emit_initializer(initializer, m.member_type, None))]
            };

            for (sub_idx, op) in value {
                field_operands.push((flat_base + sub_idx, op));
            }

            current_pos = if is_union { members.len() } else { field_idx + 1 };
        }
        field_operands
    }

    fn should_recurse_aggregate(&self, target_ty: QualType, initializer: NodeRef) -> bool {
        let kind = &self.registry.get(target_ty.ty()).kind;
        if !matches!(kind, TypeKind::Record { .. } | TypeKind::Array { .. }) {
            return false;
        }

        let init_kind = self.ast.get_kind(initializer);
        if matches!(init_kind, NodeKind::InitializerList(_)) {
            return false;
        }

        if let NodeKind::Literal(literal::Literal::String(_)) = init_kind
            && let TypeKind::Array { element_type, .. } = kind
            && self.registry.is_char_type(*element_type)
        {
            return false;
        }

        let is_compatible = self.ast.get_resolved_type(initializer).is_some_and(|ty| {
            self.registry
                .is_compatible(QualType::unqualified(ty.ty()), QualType::unqualified(target_ty.ty()))
        });

        !is_compatible
    }

    fn emit_initializer_with_path_recursive(
        &mut self,
        path: &[usize],
        extra_designators: Option<&mut dyn Iterator<Item = NodeRef>>,
        initializer: NodeRef,
        target_ty: QualType,
    ) -> Vec<(usize, Operand)> {
        if path.is_empty() {
            let op = if let Some(designators) = extra_designators {
                self.emit_initializer_with_designators(designators, initializer, target_ty, None)
            } else {
                self.emit_initializer(initializer, target_ty, None)
            };
            return vec![(0, op)];
        }

        let target_type = self.registry.get(target_ty.ty()).into_owned();
        let members = match &target_type.kind {
            TypeKind::Record { members, .. } => members.clone(),
            _ => panic!("Expected record type for designator path"),
        };

        let field_idx = path[0];
        let mut flat_offset = 0;
        for member in members.iter().take(field_idx) {
            flat_offset += self.count_flattened_members(member);
        }

        let sub_fields = self.emit_initializer_with_path_recursive(
            &path[1..],
            extra_designators,
            initializer,
            members[field_idx].member_type,
        );

        sub_fields
            .into_iter()
            .map(|(idx, op)| (flat_offset + idx, op))
            .collect()
    }

    fn resolve_designator_range(&mut self, designator_ref: NodeRef) -> (usize, usize) {
        match self.ast.get_kind(designator_ref) {
            NodeKind::Designator(Designator::ArrayIndex(idx_expr)) => {
                let idx = self.evaluate_constant_usize(*idx_expr, "Array designator must be constant");
                (idx, idx)
            }
            NodeKind::Designator(Designator::GnuArrayRange(start, end)) => {
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

    fn emit_array_initializer(
        &mut self,
        list_data: &ast::nodes::InitializerListData,
        element_ty: QualType,
        size: usize,
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        let range = list_data.init_start.range(list_data.init_len);
        let mut iter = range.peekable();
        self.emit_array_initializer_from_iter(&mut iter, None, element_ty, size, target_ty, destination)
    }

    fn emit_array_initializer_from_iter(
        &mut self,
        iter: &mut Peekable<impl Iterator<Item = NodeRef>>,
        pending_initializer: Option<NodeRef>,
        element_ty: QualType,
        size: usize,
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        let mut elements: Vec<Option<Operand>> = vec![None; size];
        let mut current_idx = 0;
        let mut first_item_processed = false;

        loop {
            // Determine next item
            let (item_ref, is_pending) = if let Some(pending) = pending_initializer
                && !first_item_processed
            {
                first_item_processed = true;
                (pending, true)
            } else if let Some(r) = iter.peek() {
                (*r, false)
            } else {
                break;
            };

            let (initializer, designator_info) = if is_pending {
                (item_ref, None)
            } else {
                let NodeKind::InitializerItem(init) = self.ast.get_kind(item_ref) else {
                    iter.next();
                    continue;
                };
                (
                    init.initializer,
                    if init.designator_len > 0 {
                        Some((init.designator_start, init.designator_len))
                    } else {
                        None
                    },
                )
            };

            // Stop if we have filled the array with positional initializers
            if designator_info.is_none() && size > 0 && current_idx >= size {
                break;
            }

            let (start, end) = if let Some((d_start, _)) = designator_info {
                match self.ast.get_kind(d_start) {
                    NodeKind::Designator(Designator::ArrayIndex(_))
                    | NodeKind::Designator(Designator::GnuArrayRange(_, _)) => self.resolve_designator_range(d_start),
                    _ => {
                        // Field designator or other. Not for array.
                        if !is_pending {
                            break;
                        }
                        panic!("Field designator in array initializer");
                    }
                }
            } else {
                (current_idx, current_idx)
            };

            if !is_pending {
                iter.next();
            }

            let operand = if let Some((d_start, d_len)) = designator_info
                && d_len > 1
            {
                let range = d_start.range(d_len);
                let sub_iter = range.skip(1);
                self.emit_initializer_with_designators(sub_iter, initializer, element_ty, None)
            } else if self.should_recurse_aggregate(element_ty, initializer) {
                match &self.registry.get(element_ty.ty()).kind {
                    TypeKind::Record { .. } => {
                        let fields = self.emit_struct_fields_recursive(iter, Some(initializer), element_ty);
                        self.finalize_struct_initializer(fields, element_ty, None)
                    }
                    TypeKind::Array {
                        element_type: inner_elem,
                        size: inner_size,
                    } => {
                        let array_size = if let ArraySizeType::Constant(s) = inner_size {
                            *s
                        } else {
                            0
                        };
                        self.emit_array_initializer_from_iter(
                            iter,
                            Some(initializer),
                            QualType::unqualified(*inner_elem),
                            array_size,
                            element_ty,
                            None,
                        )
                    }
                    _ => unreachable!(),
                }
            } else {
                self.emit_initializer(initializer, element_ty, None)
            };
            if end >= elements.len() {
                elements.resize(end + 1, None);
            }
            for item in elements.iter_mut().take(end + 1).skip(start) {
                *item = Some(operand.clone());
            }
            current_idx = end + 1;
        }

        let mir_elem_ty = self.lower_qual_type(element_ty);
        let final_elements = elements
            .into_iter()
            .map(|op| op.unwrap_or_else(|| Operand::Constant(self.create_constant(mir_elem_ty, ConstValueKind::Zero))))
            .collect();

        self.finalize_array_initializer(final_elements, target_ty, destination)
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
        if self.current_function.is_none() {
            let const_kind = create_const(self, data);
            Operand::Constant(self.create_constant(mir_ty, const_kind))
        } else if let Some(place) = destination {
            let rval = create_rvalue(data);
            self.mir_builder
                .add_statement(crate::mir::MirStmt::Assign(place.clone(), rval));
            Operand::Copy(Box::new(place))
        } else {
            let rval = create_rvalue(data);
            self.emit_rvalue_to_operand(rval, mir_ty)
        }
    }

    fn finalize_struct_initializer(
        &mut self,
        field_operands: Vec<(usize, Operand)>,
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        // Dedup by index, taking the last one for each index
        let mut final_fields: Vec<(usize, Operand)> = Vec::new();
        for (idx, op) in field_operands {
            if let Some(existing) = final_fields.iter_mut().find(|(i, _)| *i == idx) {
                existing.1 = op;
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

    fn finalize_array_initializer(
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

    pub(crate) fn emit_initializer(
        &mut self,
        init_ref: NodeRef,
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        let kind = *self.ast.get_kind(init_ref);
        let target_type = self.registry.get(target_ty.ty()).into_owned();

        match (&kind, &target_type.kind) {
            (NodeKind::InitializerList(list), TypeKind::Record { .. }) => {
                self.emit_initializer_list(list, target_ty, destination)
            }
            (NodeKind::InitializerList(list), TypeKind::Array { element_type, size }) => {
                let array_size = if let ArraySizeType::Constant(s) = size { *s } else { 0 };
                self.emit_array_initializer(
                    list,
                    QualType::unqualified(*element_type),
                    array_size,
                    target_ty,
                    destination,
                )
            }
            // ...
            (NodeKind::Literal(literal::Literal::String(val)), TypeKind::Array { element_type, size }) => {
                let fixed_size = if let ArraySizeType::Constant(s) = size {
                    Some(*s)
                } else {
                    None
                };
                Operand::Constant(self.create_array_const_from_string(
                    val,
                    fixed_size,
                    Some(QualType::unqualified(*element_type)),
                ))
            }
            (NodeKind::InitializerList(list), _) => {
                if list.init_len == 0 {
                    let mir_ty = self.lower_qual_type(target_ty);
                    return Operand::Constant(self.create_constant(mir_ty, ConstValueKind::Zero));
                }
                let NodeKind::InitializerItem(item) = self.ast.get_kind(list.init_start) else {
                    unreachable!()
                };
                self.emit_initializer(item.initializer, target_ty, destination)
            }
            _ => {
                let operand = self.emit_expression(init_ref, true);
                let mir_target_ty = self.lower_qual_type(target_ty);

                if self.get_operand_type(&operand) == mir_target_ty {
                    return operand;
                }

                // Brace elision: scalar -> aggregate
                self.emit_brace_elision(operand, init_ref, target_ty, destination)
            }
        }
    }

    pub(crate) fn create_array_const_from_string(
        &mut self,
        val: &ast::NameId,
        fixed_size: Option<usize>,
        elem_ty: Option<QualType>,
    ) -> crate::mir::ConstValueId {
        let parsed = crate::semantic::literal_utils::parse_string_literal(*val);
        let size = fixed_size.unwrap_or(parsed.size);

        let (mir_elem_ty, layout) = if let Some(qt) = elem_ty {
            (self.lower_qual_type(qt), self.registry.get_layout(qt.ty()).into_owned())
        } else {
            let ty_ref = self.registry.get_builtin_type(parsed.builtin_type);
            (
                self.lower_qual_type(QualType::unqualified(ty_ref)),
                self.registry.get_layout(ty_ref).into_owned(),
            )
        };

        let constants = (0..size)
            .map(|i| {
                let v = parsed.values.get(i).cloned().unwrap_or(0);
                self.create_constant(mir_elem_ty, ConstValueKind::Int(v))
            })
            .collect();

        let array_ty = self.mir_builder.add_type(MirType::Array {
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

    pub(crate) fn emit_literal_string(&mut self, val: &ast::NameId, ty: QualType) -> Operand {
        let mir_ty = self.lower_qual_type(ty);
        let elem_ty = match &self.registry.get(ty.ty()).kind {
            TypeKind::Array { element_type, .. } => *element_type,
            _ => self.registry.type_char,
        };

        let array_const = self.create_array_const_from_string(val, None, Some(QualType::unqualified(elem_ty)));
        let name = self.mir_builder.get_next_anonymous_global_name();
        let global = self
            .mir_builder
            .create_global_with_init(name, mir_ty, true, Some(array_const));

        Operand::Constant(self.create_constant(mir_ty, ConstValueKind::GlobalAddress(global)))
    }

    pub(crate) fn emit_compound_literal(&mut self, ty: QualType, init_ref: NodeRef) -> Operand {
        let mir_ty = self.lower_qual_type(ty);

        if self.current_function.is_none() {
            let init_const = self
                .eval_initializer_to_const(init_ref, ty)
                .expect("Global compound literal init must be const");
            let name = self.mir_builder.get_next_anonymous_global_name();
            let global = self
                .mir_builder
                .create_global_with_init(name, mir_ty, false, Some(init_const));
            Operand::Copy(Box::new(Place::Global(global)))
        } else {
            let (_, place) = self.create_temp_local(mir_ty);
            let init_op = self.emit_initializer(init_ref, ty, Some(place.clone()));
            self.emit_assignment(place.clone(), init_op);
            Operand::Copy(Box::new(place))
        }
    }

    pub(crate) fn eval_initializer_to_const(
        &mut self,
        init_ref: NodeRef,
        ty: QualType,
    ) -> Option<crate::mir::ConstValueId> {
        let operand = self.emit_initializer(init_ref, ty, None);
        self.operand_to_const_id(&operand)
    }

    fn emit_initializer_with_designators(
        &mut self,
        mut designators: impl Iterator<Item = NodeRef>,
        initializer: NodeRef,
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        let designator_ref = if let Some(d) = designators.next() {
            d
        } else {
            return self.emit_initializer(initializer, target_ty, destination);
        };

        let target_type = self.registry.get(target_ty.ty()).into_owned();

        match &target_type.kind {
            TypeKind::Array { element_type, size } => {
                let (start, end) = self.resolve_designator_range(designator_ref);
                let array_size = if let ArraySizeType::Constant(s) = size { *s } else { 0 };

                let sub_op = self.emit_initializer_with_designators(
                    designators,
                    initializer,
                    QualType::unqualified(*element_type),
                    None,
                );

                let mut elements = vec![None; array_size];
                for (i, element) in elements.iter_mut().enumerate().take(end + 1).skip(start) {
                    if i < array_size {
                        *element = Some(sub_op.clone());
                    }
                }

                let mir_elem_ty = self.lower_qual_type(QualType::unqualified(*element_type));
                let zero_op = Operand::Constant(self.create_constant(mir_elem_ty, ConstValueKind::Zero));

                self.finalize_array_initializer(
                    elements.into_iter().map(|e| e.unwrap_or(zero_op.clone())).collect(),
                    target_ty,
                    destination,
                )
            }
            TypeKind::Record { .. } => {
                let (flat_members, _) = self.get_flattened_type_info(target_ty.ty());
                let NodeKind::Designator(Designator::FieldName(name)) = self.ast.get_kind(designator_ref) else {
                    panic!("Expected field name designator for record");
                };

                let field_idx = flat_members
                    .iter()
                    .position(|m| m.name == Some(*name))
                    .expect("Unknown field in designator");

                let value = self.emit_initializer_with_designators(
                    designators,
                    initializer,
                    flat_members[field_idx].member_type,
                    None,
                );

                self.finalize_struct_initializer(vec![(field_idx, value)], target_ty, destination)
            }
            _ => panic!("Designator on non-aggregate type"),
        }
    }
    fn emit_brace_elision(
        &mut self,
        operand: Operand,
        init_ref: NodeRef,
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        let target_type = self.registry.get(target_ty.ty()).into_owned();
        match &target_type.kind {
            TypeKind::Array { element_type, size } => {
                let elem_ty = QualType::unqualified(*element_type);
                let final_op = self.emit_brace_elision(operand, init_ref, elem_ty, None);
                let mir_elem_ty = self.lower_qual_type(elem_ty);
                let len = if let ArraySizeType::Constant(l) = size { *l } else { 1 };
                let mut elements = vec![final_op];
                while elements.len() < len {
                    elements.push(Operand::Constant(
                        self.create_constant(mir_elem_ty, ConstValueKind::Zero),
                    ));
                }
                self.finalize_array_initializer(elements, target_ty, destination)
            }
            TypeKind::Record { .. } if !target_type.is_record_empty() => {
                let (flat_members, _) = self.get_flattened_type_info(target_ty.ty());
                if flat_members.is_empty() {
                    let mir_target_ty = self.lower_qual_type(target_ty);
                    return Operand::Constant(self.create_constant(mir_target_ty, ConstValueKind::Zero));
                }
                let member_ty = flat_members[0].member_type;
                let final_op = self.emit_brace_elision(operand, init_ref, member_ty, None);
                self.finalize_struct_initializer(vec![(0, final_op)], target_ty, destination)
            }
            _ => {
                let mir_target_ty = self.lower_qual_type(target_ty);
                let conv_op = self.apply_conversions(operand, init_ref, mir_target_ty);
                if self.get_operand_type(&conv_op) != mir_target_ty {
                    Operand::Cast(mir_target_ty, Box::new(conv_op))
                } else {
                    conv_op
                }
            }
        }
    }

    fn count_flattened_members(&self, m: &StructMember) -> usize {
        if m.name.is_some() {
            return 1;
        }
        let ty_ref = m.member_type.ty();
        if !ty_ref.is_record() {
            return 1;
        }
        let mut flat_members = Vec::new();
        let mut flat_offsets = Vec::new();
        let type_obj = self.registry.get(ty_ref);
        type_obj.flatten_members_with_layouts(self.registry, &mut flat_members, &mut flat_offsets, 0);
        flat_members.len()
    }

    fn find_member_recursive(&self, members: &[StructMember], name: crate::ast::NameId) -> Option<(usize, Vec<usize>)> {
        for (i, m) in members.iter().enumerate() {
            if m.name == Some(name) {
                return Some((i, Vec::new()));
            }
            if m.name.is_none() {
                // Anonymous member: look inside
                let sub_ty = self.registry.get(m.member_type.ty());
                if let TypeKind::Record {
                    members: sub_members, ..
                } = &sub_ty.kind
                    && let Some((sub_idx, mut path)) = self.find_member_recursive(sub_members, name)
                {
                    path.insert(0, sub_idx);
                    return Some((i, path));
                }
            }
        }
        None
    }
}
