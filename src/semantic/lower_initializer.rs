use crate::ast;
use crate::ast::{Designator, NameId, NodeKind, NodeRef, literal};
use crate::mir::{ConstValueId, ConstValueKind, MirArrayLayout, MirType, Operand, Place, Rvalue};
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
        let mut current_field_idx = 0;

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
                let idx = current_field_idx;
                current_field_idx += 1;
                idx
            };

            if field_idx >= members.len() {
                // Ignore excess initializers
                continue;
            }

            let member_ty = members[field_idx].member_type;

            let operand = self.lower_initializer(init.initializer, member_ty, None);
            field_operands.push((field_idx, operand));
            if field_idx < field_offsets.len() {
                let target_kind = &self.registry.get(target_ty.ty()).kind;
                let is_union_container = matches!(target_kind, TypeKind::Record { is_union: true, .. });

                if is_union_container {
                    current_field_idx = members.len();
                } else {
                    let base_offset = field_offsets[field_idx];
                    let member_ty = members[field_idx].member_type;
                    let member_ty_ref = member_ty.ty();
                    let member_kind = &self.registry.get(member_ty_ref).kind;
                    let member_size = if let TypeKind::Array {
                        size: ArraySizeType::Incomplete,
                        ..
                    } = member_kind
                    {
                        0
                    } else {
                        self.registry.get_layout(member_ty_ref).size
                    };
                    let is_bitfield = members[field_idx].bit_field_size.is_some();

                    let mut next_idx = field_idx + 1;

                    // Only skip overlapping fields if current field is NOT empty struct and NOT bitfield.
                    // This is heuristic for Anonymous Union members inside a Struct.
                    let should_skip = !is_bitfield && member_size > 0;

                    if should_skip {
                        while next_idx < field_offsets.len() && field_offsets[next_idx] == base_offset {
                            next_idx += 1;
                        }
                    }
                    current_field_idx = next_idx;
                }
            }
        }

        self.finalize_struct_initializer(field_operands, target_ty, destination)
    }

    pub(crate) fn resolve_designator_range(&mut self, designator_ref: NodeRef) -> (usize, usize) {
        match self.ast.get_kind(designator_ref) {
            NodeKind::Designator(Designator::ArrayIndex(idx_expr)) => {
                let idx =
                    self.evaluate_constant_usize(*idx_expr, "Array designator must be an integer constant expression");
                (idx, idx)
            }
            NodeKind::Designator(Designator::GnuArrayRange(start_expr, end_expr)) => {
                let start = self
                    .evaluate_constant_usize(*start_expr, "Array range start must be an integer constant expression");
                let end =
                    self.evaluate_constant_usize(*end_expr, "Array range end must be an integer constant expression");

                if end < start {
                    panic!("Array range end must be >= start");
                }
                (start, end)
            }
            NodeKind::Designator(Designator::FieldName(_)) => {
                panic!("Field designator for array initializer");
            }
            _ => {
                panic!("Unsupported designator for array initializer");
            }
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

            let (range_start, range_end) = if init.designator_len > 0 {
                // We only look at the first designator for the array index.
                // Nested designators would need to be handled by constructing
                // partial initializers, but for now we assume 1D array or first level.
                self.resolve_designator_range(init.designator_start)
            } else {
                (current_idx, current_idx)
            };

            let operand = self.lower_initializer(init.initializer, element_ty, None);

            for i in range_start..=range_end {
                // Ensure elements vector is large enough
                if i >= elements.len() {
                    elements.resize(i + 1, None);
                }
                elements[i] = Some(operand.clone());
            }

            // Advance index for next positional initializer
            current_idx = range_end + 1;
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
                let mut flat_offsets = Vec::new();
                target_type.flatten_members_with_layouts(self.registry, &mut flat_members, &mut flat_offsets, 0);
                self.lower_initializer_list(&list, &flat_members, &flat_offsets, target_ty, destination)
            }
            (NodeKind::InitializerList(list), TypeKind::Array { element_type, size }) => {
                let element_ty = QualType::unqualified(*element_type);
                let array_size = if let ArraySizeType::Constant(s) = size { *s } else { 0 };
                self.lower_array_initializer(&list, element_ty, array_size, target_ty, destination)
            }
            (NodeKind::Literal(literal::Literal::String(val)), TypeKind::Array { element_type, size }) => {
                let fixed_size = if let ArraySizeType::Constant(s) = size {
                    Some(*s)
                } else {
                    None
                };
                let array_const_id =
                    self.create_array_const_from_string(&val, fixed_size, Some(QualType::unqualified(*element_type)));
                Operand::Constant(array_const_id)
            }
            (NodeKind::InitializerList(list), _) => {
                // Handle scalar initialization with braces: int x = { 1 };
                if list.init_len == 1 {
                    let first_item_ref = list.init_start;
                    if let NodeKind::InitializerItem(item) = self.ast.get_kind(first_item_ref) {
                        if item.designator_len > 0 {
                            // C11 6.7.9p11: The initializer for a scalar shall be a single expression, optionally enclosed in braces.
                            // GCC warns about designators here, but we can perhaps support it or error.
                            // For now, assume positional.
                            panic!("Designators in scalar initializer not supported");
                        }
                        self.lower_initializer(item.initializer, target_ty, destination)
                    } else {
                        unreachable!("Initializer list contains non-InitializerItem");
                    }
                } else {
                    // Check if it's an empty list {} which is allowed in GCC/C23 as zero-init
                    if list.init_len == 0 {
                        // Return 0 constant
                        let mir_ty = self.lower_qual_type(target_ty);
                        Operand::Constant(self.create_constant(mir_ty, ConstValueKind::Zero))
                    } else {
                        // Excess elements for scalar?
                        // int x = { 1, 2 };
                        // We should use the first one and warn/ignore the rest?
                        // GCC warns: "excess elements in scalar initializer"
                        // So we should take the first one.

                        let first_item_ref = list.init_start;
                        if let NodeKind::InitializerItem(item) = self.ast.get_kind(first_item_ref) {
                            self.lower_initializer(item.initializer, target_ty, destination)
                        } else {
                            unreachable!();
                        }
                    }
                }
            }
            _ => {
                let operand = self.lower_expression(init_ref, true);
                let mir_target_ty = self.lower_qual_type(target_ty);

                // If the operand is already of the target type (e.g. struct copy),
                // use it directly instead of attempting brace elision.
                // This handles cases like `struct S s = (struct S){...};`
                let current_ty = self.get_operand_type(&operand);
                if current_ty == mir_target_ty {
                    return operand;
                }

                // Check for scalar -> aggregate initialization (brace elision)
                let target_kind = self.registry.get(target_ty.ty()).kind.clone();
                match target_kind {
                    TypeKind::Array { element_type, size } => {
                        // Initialize first element with operand, rest with 0
                        let element_qt = QualType::unqualified(element_type);
                        let mir_elem_ty = self.lower_qual_type(element_qt);
                        // Apply conversions to element type
                        let operand = self.apply_conversions(operand, init_ref, mir_elem_ty);
                        let operand = if self.get_operand_type(&operand) != mir_elem_ty {
                            Operand::Cast(mir_elem_ty, Box::new(operand))
                        } else {
                            operand
                        };

                        let array_len = if let ArraySizeType::Constant(len) = size {
                            len
                        } else {
                            1
                        };

                        let mut elements = vec![Some(operand)];
                        if array_len > 1 {
                            elements.resize(array_len, None);
                        }

                        // Fill gaps with zero
                        let final_elements = elements
                            .into_iter()
                            .map(|op| {
                                op.unwrap_or_else(|| {
                                    Operand::Constant(self.create_constant(mir_elem_ty, ConstValueKind::Zero))
                                })
                            })
                            .collect();

                        return self.finalize_array_initializer(final_elements, target_ty, destination);
                    }
                    TypeKind::Record { members, .. } => {
                        // Initialize first field with operand, rest with 0
                        if let Some(first_member) = members.first() {
                            let member_qt = first_member.member_type;
                            let mir_member_ty = self.lower_qual_type(member_qt);
                            // Apply conversions
                            let operand = self.apply_conversions(operand, init_ref, mir_member_ty);
                            let operand = if self.get_operand_type(&operand) != mir_member_ty {
                                Operand::Cast(mir_member_ty, Box::new(operand))
                            } else {
                                operand
                            };

                            // We only have the first operand.
                            let field_operands = vec![(0, operand)];
                            return self.finalize_struct_initializer(field_operands, target_ty, destination);
                        }
                    }
                    _ => {}
                }

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

    pub(crate) fn create_array_const_from_string(
        &mut self,
        val: &NameId,
        fixed_size: Option<usize>,
        elem_ty: Option<QualType>,
    ) -> ConstValueId {
        let parsed = crate::semantic::literal_utils::parse_string_literal(*val);

        let size = fixed_size.unwrap_or(parsed.size);

        // Determine MIR type for elements and layout
        let (mir_elem_ty, elem_layout) = if let Some(qt) = elem_ty {
            let layout = self.registry.get_layout(qt.ty()).into_owned();
            (self.lower_qual_type(qt), layout)
        } else {
            // Fallback based on parsed type
            let ty_ref = self.registry.get_builtin_type(parsed.builtin_type);
            let layout = self.registry.get_layout(ty_ref).into_owned();
            (self.lower_qual_type(QualType::unqualified(ty_ref)), layout)
        };

        let mut constants = Vec::with_capacity(size);
        for i in 0..size {
            let val = if i < parsed.values.len() { parsed.values[i] } else { 0 };
            constants.push(self.create_constant(mir_elem_ty, ConstValueKind::Int(val)));
        }

        let align = elem_layout.alignment;
        let stride = elem_layout.size;
        // let total_size = (stride as usize * size) as u16;

        let array_ty = self.mir_builder.add_type(MirType::Array {
            element: mir_elem_ty,
            size,
            layout: MirArrayLayout {
                size: 0, // Mimic old behavior
                align,
                stride,
            },
        });

        self.create_constant(array_ty, ConstValueKind::ArrayLiteral(constants))
    }

    pub(crate) fn lower_literal_string(&mut self, val: &NameId, ty: QualType) -> Operand {
        let string_type = self.lower_qual_type(ty);
        // Extract element type from ty to ensure correct constant type
        let element_type = match &self.registry.get(ty.ty()).kind {
            TypeKind::Array { element_type, .. } => *element_type,
            _ => self.registry.type_char, // Should not happen for string literal
        };

        let array_const_id = self.create_array_const_from_string(val, None, Some(QualType::unqualified(element_type)));

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
