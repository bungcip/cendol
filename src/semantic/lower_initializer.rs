use crate::ast;
use crate::ast::{Designator, NodeKind, NodeRef, literal};
use crate::mir::{ConstValueKind, MirArrayLayout, MirType, Operand, Place, Rvalue};
use crate::semantic::ast_to_mir::AstToMirLowerer;
use crate::semantic::{ArraySizeType, QualType, StructMember, TypeKind};

impl<'a> AstToMirLowerer<'a> {
    pub(crate) fn lower_initializer_list(
        &mut self,
        list_data: &ast::nodes::InitializerListData,
        members: &[StructMember],
        field_offsets: &[u16],
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        let mut field_operands = Vec::new();
        let mut current_pos = 0;

        for item_ref in list_data.init_start.range(list_data.init_len) {
            let NodeKind::InitializerItem(init) = self.ast.get_kind(item_ref) else {
                continue;
            };

            let field_idx = if init.designator_len > 0 {
                let NodeKind::Designator(Designator::FieldName(name)) = self.ast.get_kind(init.designator_start) else {
                    panic!("Array designator in struct initializer");
                };
                members
                    .iter()
                    .position(|m| m.name == Some(*name))
                    .expect("Unknown field in designator")
            } else {
                current_pos
            };

            if field_idx >= members.len() {
                continue;
            }

            let operand = if init.designator_len > 1 {
                let range = init.designator_start.range(init.designator_len);
                let iter = range.skip(1);
                self.lower_initializer_with_designators(iter, init.initializer, members[field_idx].member_type, None)
            } else {
                self.lower_initializer(init.initializer, members[field_idx].member_type, None)
            };
            field_operands.push((field_idx, operand));

            // Update positional index for next elements
            if field_idx < field_offsets.len() {
                let is_union = matches!(
                    self.registry.get(target_ty.ty()).kind,
                    TypeKind::Record { is_union: true, .. }
                );
                if is_union {
                    current_pos = members.len(); // Stop positional init after one union member
                } else {
                    let base_offset = field_offsets[field_idx];
                    let m_ty = members[field_idx].member_type.ty();
                    let m_kind = &self.registry.get(m_ty).kind;
                    let m_size = if matches!(
                        m_kind,
                        TypeKind::Array {
                            size: ArraySizeType::Incomplete,
                            ..
                        }
                    ) {
                        0
                    } else {
                        self.registry.get_layout(m_ty).size
                    };

                    // Skip overlapping fields (for anonymous unions) and handle bitfields
                    let mut next = field_idx + 1;
                    if members[field_idx].bit_field_size.is_none() && m_size > 0 {
                        while next < field_offsets.len() && field_offsets[next] == base_offset {
                            next += 1;
                        }
                    }
                    current_pos = next;
                }
            }
        }

        self.finalize_struct_initializer(field_operands, target_ty, destination)
    }

    pub(crate) fn resolve_designator_range(&mut self, designator_ref: NodeRef) -> (usize, usize) {
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

    pub(crate) fn lower_array_initializer(
        &mut self,
        list_data: &ast::nodes::InitializerListData,
        element_ty: QualType,
        size: usize,
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        let mut elements: Vec<Option<Operand>> = vec![None; size];
        let mut current_idx = 0;

        for item_ref in list_data.init_start.range(list_data.init_len) {
            let NodeKind::InitializerItem(init) = self.ast.get_kind(item_ref) else {
                continue;
            };

            let (start, end) = if init.designator_len > 0 {
                self.resolve_designator_range(init.designator_start)
            } else {
                (current_idx, current_idx)
            };

            let operand = if init.designator_len > 1 {
                let range = init.designator_start.range(init.designator_len);
                let iter = range.skip(1);
                self.lower_initializer_with_designators(iter, init.initializer, element_ty, None)
            } else {
                self.lower_initializer(init.initializer, element_ty, None)
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

    pub(crate) fn finalize_initializer_generic<T, C, R>(
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

    pub(crate) fn finalize_struct_initializer(
        &mut self,
        field_operands: Vec<(usize, Operand)>,
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        self.finalize_initializer_generic(
            target_ty,
            field_operands,
            |this, ops| {
                let const_fields = ops
                    .into_iter()
                    .map(|(idx, op)| (idx, this.operand_to_const_id_strict(op, "Global struct init error")))
                    .collect();
                ConstValueKind::StructLiteral(const_fields)
            },
            Rvalue::StructLiteral,
            destination,
        )
    }

    pub(crate) fn finalize_array_initializer(
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

    pub(crate) fn lower_initializer(
        &mut self,
        init_ref: NodeRef,
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        let kind = self.ast.get_kind(init_ref).clone();
        let target_type = self.registry.get(target_ty.ty()).into_owned();

        match (&kind, &target_type.kind) {
            (NodeKind::InitializerList(list), TypeKind::Record { .. }) => {
                let (mut members, mut offsets) = (Vec::new(), Vec::new());
                target_type.flatten_members_with_layouts(self.registry, &mut members, &mut offsets, 0);
                self.lower_initializer_list(list, &members, &offsets, target_ty, destination)
            }
            (NodeKind::InitializerList(list), TypeKind::Array { element_type, size }) => {
                let array_size = if let ArraySizeType::Constant(s) = size { *s } else { 0 };
                self.lower_array_initializer(
                    list,
                    QualType::unqualified(*element_type),
                    array_size,
                    target_ty,
                    destination,
                )
            }
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
                self.lower_initializer(item.initializer, target_ty, destination)
            }
            _ => {
                let operand = self.lower_expression(init_ref, true);
                let mir_target_ty = self.lower_qual_type(target_ty);

                if self.get_operand_type(&operand) == mir_target_ty {
                    return operand;
                }

                // Brace elision: scalar -> aggregate
                self.lower_brace_elision(operand, init_ref, target_ty, destination)
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

    pub(crate) fn lower_literal_string(&mut self, val: &ast::NameId, ty: QualType) -> Operand {
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

    pub(crate) fn lower_compound_literal(&mut self, ty: QualType, init_ref: NodeRef) -> Operand {
        let mir_ty = self.lower_qual_type(ty);

        if self.current_function.is_none() {
            let init_const = self
                .lower_initializer_to_const(init_ref, ty)
                .expect("Global compound literal init must be const");
            let name = self.mir_builder.get_next_anonymous_global_name();
            let global = self
                .mir_builder
                .create_global_with_init(name, mir_ty, false, Some(init_const));
            Operand::Copy(Box::new(Place::Global(global)))
        } else {
            let (_, place) = self.create_temp_local(mir_ty);
            let init_op = self.lower_initializer(init_ref, ty, Some(place.clone()));
            self.emit_assignment(place.clone(), init_op);
            Operand::Copy(Box::new(place))
        }
    }

    pub(crate) fn lower_initializer_to_const(
        &mut self,
        init_ref: NodeRef,
        ty: QualType,
    ) -> Option<crate::mir::ConstValueId> {
        let operand = self.lower_initializer(init_ref, ty, None);
        self.operand_to_const_id(operand)
    }

    fn lower_initializer_with_designators(
        &mut self,
        mut designators: impl Iterator<Item = NodeRef>,
        initializer: NodeRef,
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        let designator = if let Some(d) = designators.next() {
            d
        } else {
            return self.lower_initializer(initializer, target_ty, destination);
        };

        let target_type = self.registry.get(target_ty.ty()).into_owned();

        match &target_type.kind {
            TypeKind::Record { members, .. } => {
                let member_idx =
                    if let NodeKind::Designator(Designator::FieldName(name)) = self.ast.get_kind(designator) {
                        members
                            .iter()
                            .position(|m| m.name == Some(*name))
                            .expect("Unknown field in designator")
                    } else {
                        panic!("Expected field designator for struct initialization");
                    };

                let member_ty = members[member_idx].member_type;
                let sub_op = self.lower_initializer_with_designators(designators, initializer, member_ty, None);

                self.finalize_struct_initializer(vec![(member_idx, sub_op)], target_ty, destination)
            }
            TypeKind::Array { element_type, size } => {
                let (start, end) = self.resolve_designator_range(designator);
                let elem_ty = QualType::unqualified(*element_type);

                let sub_op = self.lower_initializer_with_designators(designators, initializer, elem_ty, None);

                let array_len = if let ArraySizeType::Constant(s) = size {
                    *s
                } else {
                    end + 1
                };

                let mir_elem_ty = self.lower_qual_type(elem_ty);
                let zero = Operand::Constant(self.create_constant(mir_elem_ty, ConstValueKind::Zero));

                let mut elements = vec![zero; array_len];
                for item in elements.iter_mut().take(end + 1).skip(start) {
                    *item = sub_op.clone();
                }

                self.finalize_array_initializer(elements, target_ty, destination)
            }
            _ => panic!("Designator on non-aggregate type"),
        }
    }

    fn lower_brace_elision(
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
                let final_op = self.lower_brace_elision(operand, init_ref, elem_ty, None);
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
            TypeKind::Record { members, .. } if !members.is_empty() => {
                let member_ty = members[0].member_type;
                let final_op = self.lower_brace_elision(operand, init_ref, member_ty, None);
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
}
