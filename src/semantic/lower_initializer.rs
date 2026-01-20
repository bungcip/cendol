use crate::ast;
use crate::ast::{Designator, NameId, NodeKind, NodeRef};
use crate::mir::{ConstValueId, ConstValueKind, MirArrayLayout, MirType, Operand, Place, Rvalue};
use crate::semantic::ast_to_mir::AstToMirLowerer;
use crate::semantic::{ArraySizeType, BuiltinType, QualType, StructMember, TypeKind};

impl<'a> AstToMirLowerer<'a> {
    pub(crate) fn lower_initializer_list(
        &mut self,
        list_data: &ast::nodes::InitializerListData,
        members: &[StructMember],
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        let mut field_operands = Vec::new();
        let mut current_field_idx = 0;
        let (_rec_size, _rec_align, field_layouts, _) = self.registry.get_record_layout(target_ty.ty());

        for item_ref in list_data.init_start.range(list_data.init_len) {
            let NodeKind::InitializerItem(init) = self.ast.get_kind(item_ref) else {
                continue;
            };
            let init = *init;
            let field_idx = if init.designator_len > 0 {
                let designator_ref = init.designator_start;
                if let NodeKind::Designator(Designator::FieldName(name)) = self.ast.get_kind(designator_ref) {
                    members.iter().position(|m| m.name == Some(*name)).unwrap()
                } else {
                    panic!("Array designator for struct initializer");
                }
            } else {
                let mut idx = current_field_idx;
                let init_node_kind = self.ast.get_kind(init.initializer);
                if let NodeKind::InitializerList(_) = init_node_kind {
                    if idx < members.len() {
                        let mut found = None;
                        for (j, item) in members.iter().enumerate().skip(idx) {
                            let mty = item.member_type;
                            if let TypeKind::Record { .. } = &self.registry.get(mty.ty()).kind {
                                found = Some(j);
                                break;
                            }
                        }
                        if let Some(j) = found {
                            idx = j;
                            current_field_idx = j + 1;
                            idx
                        } else {
                            current_field_idx += 1;
                            idx
                        }
                    } else {
                        current_field_idx += 1;
                        idx
                    }
                } else {
                    let tmp = idx;
                    current_field_idx += 1;
                    tmp
                }
            };

            let member_ty = members[field_idx].member_type;

            let operand = self.lower_initializer(init.initializer, member_ty, None);
            field_operands.push((field_idx, operand));
            if field_idx < field_layouts.len() {
                let base_offset = field_layouts[field_idx].offset;
                let mut next_idx = field_idx + 1;
                while next_idx < field_layouts.len() && field_layouts[next_idx].offset == base_offset {
                    next_idx += 1;
                }
                current_field_idx = next_idx;
            }
        }

        self.finalize_struct_initializer(field_operands, target_ty, destination)
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

            // Handle designator
            if init.designator_len > 0 {
                let designator_ref = init.designator_start;
                // We only look at the first designator for the array index.
                // Nested designators would need to be handled by constructing
                // partial initializers, but for now we assume 1D array or first level.
                match self.ast.get_kind(designator_ref) {
                    NodeKind::Designator(Designator::ArrayIndex(idx_expr)) => {
                        let idx_operand = self.lower_expression(*idx_expr, true);
                        if let Some(const_id) = self.operand_to_const_id(idx_operand) {
                            let const_val = self.mir_builder.get_constants().get(&const_id).unwrap();
                            if let ConstValueKind::Int(val) = const_val.kind {
                                current_idx = val as usize;
                            } else {
                                panic!("Array designator must be an integer constant");
                            }
                        } else {
                            panic!("Array designator must be a constant expression");
                        }
                    }
                    // Struct field designators are invalid for arrays
                    NodeKind::Designator(Designator::FieldName(_)) => {
                        panic!("Field designator for array initializer");
                    }
                    _ => {
                        // Other designators (e.g. ranges) not supported yet
                        panic!("Unsupported designator for array initializer");
                    }
                }
            }

            // Ensure elements vector is large enough
            if current_idx >= elements.len() {
                elements.resize(current_idx + 1, None);
            }

            let operand = self.lower_initializer(init.initializer, element_ty, None);
            elements[current_idx] = Some(operand);

            // Advance index for next positional initializer
            current_idx += 1;
        }

        // Fill gaps with zero
        let final_elements = elements
            .into_iter()
            .map(|op| {
                op.unwrap_or_else(|| {
                    let mir_ty = self.lower_qual_type(element_ty);
                    Operand::Constant(self.create_constant(mir_ty, ConstValueKind::Zero))
                })
            })
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
        if self.current_function.is_none() {
            let mir_ty = self.lower_qual_type(target_ty);
            let const_kind = create_const(self, data);
            Operand::Constant(self.create_constant(mir_ty, const_kind))
        } else {
            let rval = create_rvalue(data);
            let mir_ty = self.lower_qual_type(target_ty);
            if let Some(place) = destination {
                let stmt = crate::mir::MirStmt::Assign(place.clone(), rval);
                self.mir_builder.add_statement(stmt);
                Operand::Copy(Box::new(place))
            } else {
                self.emit_rvalue_to_operand(rval, mir_ty)
            }
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
                    .map(|(idx, op)| {
                        let const_id =
                            this.operand_to_const_id_strict(op, "Global initializer is not a constant expression");
                        (idx, const_id)
                    })
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
                    .map(|op| {
                        this.operand_to_const_id_strict(op, "Global array initializer must be a constant expression")
                    })
                    .collect();
                ConstValueKind::ArrayLiteral(const_elements)
            },
            Rvalue::ArrayLiteral,
            destination,
        )
    }

    pub(crate) fn lower_initializer_to_const(&mut self, init_ref: NodeRef, ty: QualType) -> Option<ConstValueId> {
        let operand = self.lower_initializer(init_ref, ty, None);
        self.operand_to_const_id(operand)
    }

    pub(crate) fn lower_initializer(
        &mut self,
        init_ref: NodeRef,
        target_ty: QualType,
        destination: Option<Place>,
    ) -> Operand {
        let init_node_kind = self.ast.get_kind(init_ref).clone();
        let target_type = self.registry.get(target_ty.ty()).clone();

        match (init_node_kind, &target_type.kind) {
            (NodeKind::InitializerList(list), TypeKind::Record { .. }) => {
                let mut flat_members = Vec::new();
                target_type.flatten_members(self.registry, &mut flat_members);
                self.lower_initializer_list(&list, &flat_members, target_ty, destination)
            }
            (NodeKind::InitializerList(list), TypeKind::Array { element_type, size }) => {
                let element_ty = QualType::unqualified(*element_type);
                let array_size = if let ArraySizeType::Constant(s) = size { *s } else { 0 };
                self.lower_array_initializer(&list, element_ty, array_size, target_ty, destination)
            }
            (NodeKind::LiteralString(val), TypeKind::Array { element_type, size })
                if matches!(
                    self.registry.get(*element_type).kind,
                    TypeKind::Builtin(BuiltinType::Char)
                ) =>
            {
                let fixed_size = if let ArraySizeType::Constant(s) = size {
                    Some(*s)
                } else {
                    None
                };
                let array_const_id = self.create_string_array_const(&val, fixed_size);
                Operand::Constant(array_const_id)
            }
            _ => {
                let operand = self.lower_expression(init_ref, true);
                let mir_target_ty = self.lower_qual_type(target_ty);
                let operand = self.apply_conversions(operand, init_ref, mir_target_ty);

                // Ensure type match by inserting a cast if necessary
                let current_ty = self.get_operand_type(&operand);
                if current_ty != mir_target_ty {
                    Operand::Cast(mir_target_ty, Box::new(operand))
                } else {
                    operand
                }
            }
        }
    }

    pub(crate) fn create_string_array_const(&mut self, val: &NameId, fixed_size: Option<usize>) -> ConstValueId {
        let string_content = val.as_str();
        let bytes = string_content.as_bytes();
        let size = fixed_size.unwrap_or(bytes.len() + 1);

        let char_ty = self.get_char_type();

        let char_constants = (0..size)
            .map(|i| {
                let byte_val = if i < bytes.len() { bytes[i] } else { 0 };
                self.create_constant(char_ty, ConstValueKind::Int(byte_val as i64))
            })
            .collect();

        let array_ty = self.mir_builder.add_type(MirType::Array {
            element: char_ty,
            size,
            layout: MirArrayLayout {
                size: 0,
                align: 1,
                stride: 1,
            },
        });

        self.create_constant(array_ty, ConstValueKind::ArrayLiteral(char_constants))
    }

    pub(crate) fn lower_literal_string(&mut self, val: &NameId, ty: QualType) -> Operand {
        let string_type = self.lower_qual_type(ty);
        let array_const_id = self.create_string_array_const(val, None);

        let global_name = self.mir_builder.get_next_anonymous_global_name();
        let global_id = self
            .mir_builder
            .create_global_with_init(global_name, string_type, true, Some(array_const_id));

        Operand::Constant(self.create_constant(string_type, ConstValueKind::GlobalAddress(global_id)))
    }

    pub(crate) fn lower_compound_literal(&mut self, ty: QualType, init_ref: NodeRef) -> Operand {
        let mir_ty = self.lower_qual_type(ty);

        if self.current_function.is_none() {
            let global_name = self.mir_builder.get_next_anonymous_global_name();
            let init_const_id = self
                .lower_initializer_to_const(init_ref, ty)
                .expect("Global compound literal initializer must be constant");

            let global_id = self
                .mir_builder
                .create_global_with_init(global_name, mir_ty, false, Some(init_const_id));

            Operand::Copy(Box::new(Place::Global(global_id)))
        } else {
            let (_, place) = self.create_temp_local(mir_ty);
            let init_operand = self.lower_initializer(init_ref, ty, Some(place.clone()));
            self.emit_assignment(place.clone(), init_operand);
            Operand::Copy(Box::new(place))
        }
    }
}
