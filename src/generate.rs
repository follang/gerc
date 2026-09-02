use std::collections::{BTreeMap, BTreeSet};

use linc::contract::{
    CallableAbiAssessment, DeclarationEvidence, EnumLayoutEvidence, LayoutEvidence,
    ProviderAssessment, RecordLayoutEvidence, SymbolAssessment,
};
use parc::contract::{
    Architecture, ArrayBound, CDataModel, CFloatingType, CIntegerType, CType, CTypeKind,
    CallingConvention, CharSignedness, CharTypeSignedness, ClosureRequirement,
    CompleteSourcePackage, DeclarationId, ExactInteger, FloatingFormat, FunctionPrototype,
    MacroCategory, MacroForm, MacroValue, Nullability, OperatingSystem, RecordCompleteness,
    RecordKind, SignedIntegerRepresentation, Signedness, SourceDeclaration, SourceDeclarationKind,
    SourceEnum, SourceFunction, SourceMacro, SourceRecord, SourceTypeAlias, SourceVariable,
    TypeQualifiers,
};

use crate::{
    emit::parse_rust_file, fingerprint::generation_fingerprint, render_projection,
    verify_pre_lowering, verify_projection, GeneratedFile, GeneratedFileSet, GenerationBundle,
    GenerationContext, GenerationDiagnostic, GenerationError, GenerationManifest,
    GenerationRequest, GenerationResult, NativeSymbolBinding, RustAbi, RustEnum, RustEnumVariant,
    RustField, RustFunction, RustItem, RustLinkPlan, RustMacro, RustName, RustParameter,
    RustRecord, RustRecordKind, RustScalar, RustType, RustTypeAlias, RustTypeKind, RustVariable,
    RustVariableMutability, SourceDeclarationMetadata, ValidatedRustProjection,
};

/// Strict PARC + LINC -> GERC generation. There is intentionally no source-
/// only overload and no optional evidence path.
pub fn generate(request: GenerationRequest<'_>) -> GenerationResult<GenerationBundle> {
    let source = request.source().source();
    let evidence = request.evidence().package();
    let context = GenerationContext::new(
        source.fingerprint(),
        source.target_fingerprint(),
        evidence.fingerprint(),
    );
    generate_inner(request).map_err(|error| error.with_context(context))
}

fn generate_inner(request: GenerationRequest<'_>) -> GenerationResult<GenerationBundle> {
    verify_pre_lowering(&request)?;
    let source = request.source().source();
    let evidence = request.evidence().package();
    let closure = request.declaration_closure();

    let mut global_names = NameAllocator::default();
    let mut declaration_names = BTreeMap::new();
    // A `typedef struct X X;` gives the same name to the completed struct and
    // to a redundant self-alias. Rust has one name namespace, so only one item
    // can hold `X`; the other is left with a synthesized hash name. The struct
    // is what carries the fields a caller reads, so it takes the clean name and
    // the redundant alias is named after it -- otherwise the struct is spelled
    // `X_<hash>`, which no downstream author can name. This defers only that
    // exact case: an opaque struct or a pointer typedef keeps its current name.
    let is_redundant_self_alias = |declaration: &SourceDeclaration| -> bool {
        let SourceDeclarationKind::TypeAlias(alias) = &declaration.kind else {
            return false;
        };
        let CTypeKind::RecordRef(target) = &alias.target.kind else {
            return false;
        };
        let Some(record_declaration) = source.declaration(*target) else {
            return false;
        };
        let SourceDeclarationKind::Record(record) = &record_declaration.kind else {
            return false;
        };
        record.completeness == RecordCompleteness::Complete
            && match (&declaration.name, &record_declaration.name) {
                (Some(alias_name), Some(record_name)) => {
                    alias_name.normalized == record_name.normalized
                }
                _ => false,
            }
    };
    for pass_redundant in [false, true] {
        for entry in closure {
            let declaration =
                source
                    .declaration(entry.declaration())
                    .ok_or(GenerationError::MissingDeclaration {
                        declaration: entry.declaration(),
                    })?;
            if is_redundant_self_alias(declaration) != pass_redundant {
                continue;
            }
            let name = global_names.declaration_name(declaration)?;
            declaration_names.insert(declaration.id, name);
        }
    }

    let context = LoweringContext {
        source: request.source(),
        evidence: request.evidence(),
        declaration_names: &declaration_names,
    };

    let mut items = Vec::with_capacity(closure.len());
    for entry in closure {
        let declaration =
            source
                .declaration(entry.declaration())
                .ok_or(GenerationError::MissingDeclaration {
                    declaration: entry.declaration(),
                })?;
        items.push(lower_declaration(
            &context,
            declaration,
            entry.requirement(),
            &mut global_names,
        )?);
    }

    let mut diagnostics = Vec::new();
    let generation_context = GenerationContext::new(
        source.fingerprint(),
        source.target_fingerprint(),
        evidence.fingerprint(),
    );
    let macros = source
        .macros()
        .iter()
        .map(|source_macro| {
            lower_macro(
                source_macro,
                &mut global_names,
                &mut diagnostics,
                generation_context,
            )
        })
        .collect::<GenerationResult<Vec<_>>>()?;

    let expected_declarations: Vec<_> = closure.iter().map(|entry| entry.declaration()).collect();
    let projection = ValidatedRustProjection::try_new(
        source.target_fingerprint(),
        items,
        macros,
        &expected_declarations,
    )?;
    verify_projection(&projection)?;
    let rendered = render_projection(&projection);
    parse_rust_file("src/lib.rs", &rendered)?;
    let files = GeneratedFileSet::try_new(vec![GeneratedFile::utf8("src/lib.rs", rendered)?])?;
    let link_plan = RustLinkPlan::from_validated(evidence.resolved_link_plan(), source.target());
    let fingerprint = generation_fingerprint(
        generation_context,
        request.selection(),
        &projection,
        &diagnostics,
        &files,
        &link_plan,
    );
    let manifest = GenerationManifest::new(
        source.fingerprint(),
        source.target_fingerprint(),
        evidence.fingerprint(),
        fingerprint,
    );
    Ok(GenerationBundle::new(
        projection,
        files,
        link_plan,
        manifest,
        diagnostics,
    ))
}

struct LoweringContext<'a> {
    source: &'a CompleteSourcePackage,
    evidence: &'a linc::contract::ValidatedLinkAnalysis,
    declaration_names: &'a BTreeMap<DeclarationId, RustName>,
}

impl LoweringContext<'_> {
    fn declaration_evidence(
        &self,
        declaration: DeclarationId,
    ) -> GenerationResult<&DeclarationEvidence> {
        self.evidence
            .package()
            .declaration_evidence()
            .binary_search_by_key(&declaration, DeclarationEvidence::declaration)
            .ok()
            .map(|index| &self.evidence.package().declaration_evidence()[index])
            .ok_or(GenerationError::MissingDeclarationEvidence { declaration })
    }

    fn layout(&self, declaration: DeclarationId) -> GenerationResult<&LayoutEvidence> {
        self.evidence
            .package()
            .layouts()
            .binary_search_by_key(&declaration, LayoutEvidence::declaration)
            .ok()
            .map(|index| &self.evidence.package().layouts()[index])
            .ok_or(GenerationError::MissingLayoutEvidence { declaration })
    }

    fn name(&self, declaration: DeclarationId) -> GenerationResult<RustName> {
        self.declaration_names
            .get(&declaration)
            .cloned()
            .ok_or(GenerationError::MissingDeclaration { declaration })
    }
}

fn lower_declaration(
    context: &LoweringContext<'_>,
    declaration: &SourceDeclaration,
    requirement: ClosureRequirement,
    global_names: &mut NameAllocator,
) -> GenerationResult<RustItem> {
    let rust_name = context.name(declaration.id)?;
    match &declaration.kind {
        SourceDeclarationKind::Function(function) => {
            lower_function(context, declaration, rust_name, function).map(RustItem::Function)
        }
        SourceDeclarationKind::Record(record) => {
            lower_record(context, declaration, rust_name, record, requirement).map(RustItem::Record)
        }
        SourceDeclarationKind::Enum(enumeration) => {
            lower_enum(context, declaration, rust_name, enumeration, global_names)
                .map(RustItem::Enum)
        }
        SourceDeclarationKind::TypeAlias(alias) => {
            lower_alias(context, declaration, rust_name, alias).map(RustItem::TypeAlias)
        }
        SourceDeclarationKind::Variable(variable) => {
            lower_variable(context, declaration, rust_name, variable).map(RustItem::Variable)
        }
        SourceDeclarationKind::Unsupported(_) => Err(GenerationError::UnsupportedDeclaration {
            declaration: declaration.id,
            reason: "PARC marked the declaration kind unsupported",
        }),
    }
}

fn lower_function(
    context: &LoweringContext<'_>,
    declaration: &SourceDeclaration,
    rust_name: RustName,
    function: &SourceFunction,
) -> GenerationResult<RustFunction> {
    let abi = lower_calling_convention(
        declaration.id,
        &function.calling_convention,
        context.source.source().target().architecture(),
        context.source.source().target().operating_system(),
    )?;
    let variadic = match function.prototype {
        FunctionPrototype::Prototyped { variadic: false } => false,
        FunctionPrototype::Prototyped { variadic: true } => {
            return Err(GenerationError::UnsupportedDeclaration {
                declaration: declaration.id,
                reason: "C variadic call sites are not modeled by the frozen raw projection",
            });
        }
        FunctionPrototype::UnspecifiedParameters => {
            return Err(GenerationError::UnsupportedDeclaration {
                declaration: declaration.id,
                reason: "an unspecified C parameter list has no sound Rust FFI projection",
            });
        }
    };

    let declaration_evidence = context.declaration_evidence(declaration.id)?;
    match declaration_evidence.callable_abi() {
        CallableAbiAssessment::Confirmed {
            calling_convention, ..
        } if calling_convention == &function.calling_convention => {}
        _ => {
            return Err(GenerationError::UnsupportedDeclaration {
                declaration: declaration.id,
                reason: "LINC did not retain matching confirmed callable ABI evidence",
            });
        }
    }

    let return_type = lower_type(
        context,
        declaration.id,
        "function.return_type",
        &function.return_type,
    )?;
    let mut parameter_names = NameAllocator::default();
    let parameters = function
        .parameters
        .iter()
        .map(|parameter| {
            let parameter_path = format!("function.parameters[{}]", parameter.ordinal);
            let rust_name = parameter_names.local_name(
                parameter.name.as_ref().map(|name| name.normalized.as_str()),
                "parameter",
                parameter.id.as_bytes(),
            )?;
            let ty = lower_parameter_type(context, declaration.id, &parameter_path, &parameter.ty)?;
            if matches!(ty.kind, RustTypeKind::Void) {
                return Err(GenerationError::UnsupportedType {
                    declaration: declaration.id,
                    path: parameter_path,
                    reason: "void is not a parameter type",
                });
            }
            Ok(RustParameter {
                child: parameter.id,
                ordinal: parameter.ordinal,
                rust_name,
                source_name: parameter.name.clone(),
                ty,
                range: parameter.range,
                provenance: parameter.provenance.clone(),
                attributes: parameter.attributes.clone(),
                support: parameter.support.clone(),
            })
        })
        .collect::<GenerationResult<Vec<_>>>()?;

    Ok(RustFunction {
        declaration: declaration.id,
        rust_name,
        link_name: function.link_name.clone(),
        abi,
        parameters,
        return_type,
        variadic,
        symbol: native_symbol_binding(context, declaration.id)?,
        source: SourceDeclarationMetadata::from_source(declaration),
    })
}

fn lower_record(
    context: &LoweringContext<'_>,
    declaration: &SourceDeclaration,
    rust_name: RustName,
    record: &SourceRecord,
    requirement: ClosureRequirement,
) -> GenerationResult<RustRecord> {
    if requirement == ClosureRequirement::Opaque {
        return Ok(RustRecord {
            declaration: declaration.id,
            rust_name,
            kind: RustRecordKind::Opaque,
            source_kind: record.kind,
            source_completeness: record.completeness,
            fields: Vec::new(),
            size_bits: None,
            alignment_bits: None,
            packing_bits: None,
            source: SourceDeclarationMetadata::from_source(declaration),
        });
    }
    if record.completeness != RecordCompleteness::Complete {
        return Err(GenerationError::UnsupportedRecordRepresentation {
            declaration: declaration.id,
            reason: "a by-value record requires a complete definition",
        });
    }
    if record.fields.is_empty() {
        return Err(GenerationError::UnsupportedRecordRepresentation {
            declaration: declaration.id,
            reason: "empty C records are extension-dependent",
        });
    }

    let layout = match context.layout(declaration.id)? {
        LayoutEvidence::Record(layout) => layout,
        LayoutEvidence::Enum(_) => {
            return Err(GenerationError::LayoutMismatch {
                declaration: declaration.id,
                reason: "LINC retained enum layout for a record",
            });
        }
    };
    if !rust_object_size_fits(
        context.source.source().target().pointer_width(),
        layout.size_bits(),
    ) {
        return Err(GenerationError::UnsupportedRecordRepresentation {
            declaration: declaration.id,
            reason: "record exceeds Rust's target object-size limit",
        });
    }
    match record.kind {
        RecordKind::Struct => lower_natural_record(context, declaration, rust_name, record, layout),
        RecordKind::Union => lower_natural_union(context, declaration, rust_name, record, layout),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RecordFieldShape {
    offset_bits: u64,
    size_bits: u64,
    natural_alignment_bits: u64,
    measured_alignment_bits: Option<u32>,
}

/// Infer the only Rust representation family GERC certifies: natural
/// `repr(C)` or `repr(C, packed(N))` with a power-of-two byte cap. This is
/// derived from measured offsets/size/alignment rather than from attribute
/// spelling, so compiler-specific `packed` syntax never leaks across the
/// contract boundary. The nested option distinguishes natural layout from no
/// representable layout.
fn infer_packing(
    kind: RustRecordKind,
    fields: &[RecordFieldShape],
    size_bits: u64,
    alignment_bits: u32,
) -> Option<Option<u32>> {
    if representation_matches(kind, fields, size_bits, alignment_bits, None) {
        return Some(None);
    }

    let maximum_natural = fields
        .iter()
        .map(|field| field.natural_alignment_bits)
        .max()
        .unwrap_or(8);
    let mut cap = 8_u64;
    while cap <= maximum_natural && cap <= u64::from(u32::MAX) {
        if representation_matches(kind, fields, size_bits, alignment_bits, Some(cap)) {
            return Some(Some(cap as u32));
        }
        let Some(next) = cap.checked_mul(2) else {
            break;
        };
        cap = next;
    }
    None
}

fn representation_matches(
    kind: RustRecordKind,
    fields: &[RecordFieldShape],
    size_bits: u64,
    alignment_bits: u32,
    packing_bits: Option<u64>,
) -> bool {
    let mut record_alignment = 8_u64;
    let mut cursor = 0_u64;
    let mut maximum_size = 0_u64;

    for field in fields {
        if field.natural_alignment_bits < 8 || !field.natural_alignment_bits.is_power_of_two() {
            return false;
        }
        let effective_alignment = packing_bits.map_or(field.natural_alignment_bits, |cap| {
            field.natural_alignment_bits.min(cap)
        });
        if field.measured_alignment_bits.is_some_and(|measured| {
            let measured = u64::from(measured);
            measured != field.natural_alignment_bits && measured != effective_alignment
        }) {
            return false;
        }
        record_alignment = record_alignment.max(effective_alignment);
        match kind {
            RustRecordKind::Struct => {
                let Some(offset) = align_up(cursor, effective_alignment) else {
                    return false;
                };
                if field.offset_bits != offset {
                    return false;
                }
                let Some(next) = offset.checked_add(field.size_bits) else {
                    return false;
                };
                cursor = next;
            }
            RustRecordKind::Union => {
                if field.offset_bits != 0 {
                    return false;
                }
                maximum_size = maximum_size.max(field.size_bits);
            }
            RustRecordKind::Opaque => return false,
        }
    }

    if let Some(cap) = packing_bits {
        record_alignment = record_alignment.min(cap);
    }
    let unrounded_size = match kind {
        RustRecordKind::Struct => cursor,
        RustRecordKind::Union => maximum_size,
        RustRecordKind::Opaque => return false,
    };
    align_up(unrounded_size, record_alignment) == Some(size_bits)
        && record_alignment == u64::from(alignment_bits)
}

fn lower_natural_record(
    context: &LoweringContext<'_>,
    declaration: &SourceDeclaration,
    rust_name: RustName,
    record: &SourceRecord,
    layout: &RecordLayoutEvidence,
) -> GenerationResult<RustRecord> {
    let mut field_names = NameAllocator::default();
    let mut fields = Vec::with_capacity(record.fields.len());
    let mut shapes = Vec::with_capacity(record.fields.len());

    for (field_index, field) in record.fields.iter().enumerate() {
        if field.bit_width.is_some() {
            return Err(GenerationError::UnsupportedRecordRepresentation {
                declaration: declaration.id,
                reason: "bitfields require a dedicated storage projection",
            });
        }
        let measured = layout
            .fields()
            .binary_search_by_key(&field.id, |entry| entry.child())
            .ok()
            .map(|index| &layout.fields()[index])
            .ok_or(GenerationError::LayoutMismatch {
                declaration: declaration.id,
                reason: "a source field has no measured field layout",
            })?;
        let flexible_element = match &field.ty.kind {
            CTypeKind::Array {
                element,
                bound: ArrayBound::Flexible,
                parameter_qualifiers,
            } if *parameter_qualifiers == TypeQualifiers::NONE
                && field_index + 1 == record.fields.len() =>
            {
                Some(element.as_ref())
            }
            CTypeKind::Array {
                bound: ArrayBound::Flexible,
                ..
            } => {
                return Err(GenerationError::UnsupportedRecordRepresentation {
                    declaration: declaration.id,
                    reason: "a flexible array must be the final unqualified struct field",
                });
            }
            _ => None,
        };
        let (size_bits, alignment_bits, lowered_type) = if let Some(element) = flexible_element {
            let (_, alignment_bits) = abi_size_alignment(
                context,
                declaration.id,
                "record.flexible_element",
                element,
                0,
            )?;
            (
                0,
                alignment_bits,
                RustType {
                    qualifiers: field.ty.qualifiers,
                    nullability: field.ty.nullability,
                    support: field.ty.support.clone(),
                    kind: RustTypeKind::FlexibleArray {
                        element: Box::new(lower_type(
                            context,
                            declaration.id,
                            "record.flexible_element",
                            element,
                        )?),
                    },
                },
            )
        } else {
            let (size_bits, alignment_bits) =
                abi_size_alignment(context, declaration.id, "record.field", &field.ty, 0)?;
            (
                size_bits,
                alignment_bits,
                lower_type(context, declaration.id, "record.field", &field.ty)?,
            )
        };
        let measured_size = measured.size_bits().unwrap_or(0);
        if measured_size != size_bits {
            return Err(GenerationError::LayoutMismatch {
                declaration: declaration.id,
                reason: "field size differs from the Rust primitive projection",
            });
        }
        shapes.push(RecordFieldShape {
            offset_bits: measured.offset_bits(),
            size_bits,
            natural_alignment_bits: alignment_bits,
            measured_alignment_bits: measured.alignment_bits(),
        });
        let rust_field_name = field_names.local_name(
            field.name.as_ref().map(|name| name.normalized.as_str()),
            "field",
            field.id.as_bytes(),
        )?;
        fields.push(RustField {
            child: field.id,
            rust_name: rust_field_name,
            source_name: field.name.clone(),
            ty: lowered_type,
            offset_bits: measured.offset_bits(),
            size_bits,
            alignment_bits: measured.alignment_bits(),
            range: field.range,
            provenance: field.provenance.clone(),
            attributes: field.attributes.clone(),
            support: field.support.clone(),
            identity_tokens: field.identity_tokens.clone(),
            duplicate_ordinal: field.duplicate_ordinal,
        });
    }

    let packing_bits = infer_packing(
        RustRecordKind::Struct,
        &shapes,
        layout.size_bits(),
        layout.alignment_bits(),
    )
    .ok_or(GenerationError::UnsupportedRecordRepresentation {
        declaration: declaration.id,
        reason: "measured record layout is neither natural repr(C) nor a supported packed layout",
    })?;

    Ok(RustRecord {
        declaration: declaration.id,
        rust_name,
        kind: RustRecordKind::Struct,
        source_kind: record.kind,
        source_completeness: record.completeness,
        fields,
        size_bits: Some(layout.size_bits()),
        alignment_bits: Some(layout.alignment_bits()),
        packing_bits,
        source: SourceDeclarationMetadata::from_source(declaration),
    })
}

fn lower_natural_union(
    context: &LoweringContext<'_>,
    declaration: &SourceDeclaration,
    rust_name: RustName,
    record: &SourceRecord,
    layout: &RecordLayoutEvidence,
) -> GenerationResult<RustRecord> {
    let mut field_names = NameAllocator::default();
    let mut fields = Vec::with_capacity(record.fields.len());
    let mut shapes = Vec::with_capacity(record.fields.len());

    for field in &record.fields {
        if field.bit_width.is_some() {
            return Err(GenerationError::UnsupportedRecordRepresentation {
                declaration: declaration.id,
                reason: "union bitfields require an unsupported storage projection",
            });
        }
        if matches!(
            field.ty.kind,
            CTypeKind::Array {
                bound: ArrayBound::Flexible,
                ..
            }
        ) {
            return Err(GenerationError::UnsupportedRecordRepresentation {
                declaration: declaration.id,
                reason: "a C union cannot contain a flexible-array member",
            });
        }
        let measured = layout
            .fields()
            .binary_search_by_key(&field.id, |entry| entry.child())
            .ok()
            .map(|index| &layout.fields()[index])
            .ok_or(GenerationError::LayoutMismatch {
                declaration: declaration.id,
                reason: "a source union field has no measured layout",
            })?;
        let (size_bits, alignment_bits) =
            abi_size_alignment(context, declaration.id, "union.field", &field.ty, 0)?;
        if measured.offset_bits() != 0 || measured.size_bits() != Some(size_bits) {
            return Err(GenerationError::LayoutMismatch {
                declaration: declaration.id,
                reason: "union field offset or size differs from its Rust projection",
            });
        }
        shapes.push(RecordFieldShape {
            offset_bits: 0,
            size_bits,
            natural_alignment_bits: alignment_bits,
            measured_alignment_bits: measured.alignment_bits(),
        });
        fields.push(RustField {
            child: field.id,
            rust_name: field_names.local_name(
                field.name.as_ref().map(|name| name.normalized.as_str()),
                "union_field",
                field.id.as_bytes(),
            )?,
            source_name: field.name.clone(),
            ty: lower_type(context, declaration.id, "union.field", &field.ty)?,
            offset_bits: 0,
            size_bits,
            alignment_bits: measured.alignment_bits(),
            range: field.range,
            provenance: field.provenance.clone(),
            attributes: field.attributes.clone(),
            support: field.support.clone(),
            identity_tokens: field.identity_tokens.clone(),
            duplicate_ordinal: field.duplicate_ordinal,
        });
    }
    let packing_bits = infer_packing(
        RustRecordKind::Union,
        &shapes,
        layout.size_bits(),
        layout.alignment_bits(),
    )
    .ok_or(GenerationError::UnsupportedRecordRepresentation {
        declaration: declaration.id,
        reason: "measured union layout is neither natural repr(C) nor a supported packed layout",
    })?;
    Ok(RustRecord {
        declaration: declaration.id,
        rust_name,
        kind: RustRecordKind::Union,
        source_kind: record.kind,
        source_completeness: record.completeness,
        fields,
        size_bits: Some(layout.size_bits()),
        alignment_bits: Some(layout.alignment_bits()),
        packing_bits,
        source: SourceDeclarationMetadata::from_source(declaration),
    })
}

fn lower_enum(
    context: &LoweringContext<'_>,
    declaration: &SourceDeclaration,
    rust_name: RustName,
    enumeration: &SourceEnum,
    global_names: &mut NameAllocator,
) -> GenerationResult<RustEnum> {
    let layout = match context.layout(declaration.id)? {
        LayoutEvidence::Enum(layout) => layout,
        LayoutEvidence::Record(_) => {
            return Err(GenerationError::LayoutMismatch {
                declaration: declaration.id,
                reason: "LINC retained record layout for an enum",
            });
        }
    };
    let storage = enum_storage(declaration.id, layout)?;
    if u64::from(layout.alignment_bits()) != storage.size_bits() {
        return Err(GenerationError::InvalidEnumRepresentation {
            declaration: declaration.id,
            reason: "enum alignment differs from the frozen transparent Rust scalar",
        });
    }
    let explicit_underlying_type = enumeration
        .explicit_underlying_type
        .as_ref()
        .map(|ty| lower_type(context, declaration.id, "enum.explicit_underlying_type", ty))
        .transpose()?;
    if explicit_underlying_type.as_ref().is_some_and(|ty| {
        !matches!(
            ty.kind(),
            RustTypeKind::Scalar(value) if scalar_integer_compatible(*value, storage)
        )
    }) {
        return Err(GenerationError::InvalidEnumRepresentation {
            declaration: declaration.id,
            reason: "explicit enum storage does not match the measured Rust scalar",
        });
    }

    let variants = enumeration
        .variants
        .iter()
        .map(|variant| {
            let measured = layout
                .variants()
                .binary_search_by_key(&variant.id, |entry| entry.child())
                .ok()
                .map(|index| &layout.variants()[index])
                .ok_or(GenerationError::InvalidEnumRepresentation {
                    declaration: declaration.id,
                    reason: "an enum variant has no measured value",
                })?;
            let value = match variant.value {
                parc::contract::EnumValue::Evaluated { value } => value,
                parc::contract::EnumValue::Unevaluated { .. } => {
                    return Err(GenerationError::InvalidEnumRepresentation {
                        declaration: declaration.id,
                        reason: "enum value was not evaluated by PARC",
                    });
                }
            };
            if measured.value() != &value || !integer_fits(value, storage) {
                return Err(GenerationError::InvalidEnumRepresentation {
                    declaration: declaration.id,
                    reason: "enum value differs from evidence or does not fit storage",
                });
            }
            Ok(RustEnumVariant {
                child: variant.id,
                rust_name: global_names.local_name(
                    Some(&variant.name.normalized),
                    "enum_variant",
                    variant.id.as_bytes(),
                )?,
                source_name: variant.name.clone(),
                value,
                range: variant.range,
                provenance: variant.provenance.clone(),
                attributes: variant.attributes.clone(),
                support: variant.support.clone(),
                identity_tokens: variant.identity_tokens.clone(),
                duplicate_ordinal: variant.duplicate_ordinal,
            })
        })
        .collect::<GenerationResult<Vec<_>>>()?;

    Ok(RustEnum {
        declaration: declaration.id,
        rust_name,
        storage,
        alignment_bits: layout.alignment_bits(),
        explicit_underlying_type,
        variants,
        source: SourceDeclarationMetadata::from_source(declaration),
    })
}

fn lower_alias(
    context: &LoweringContext<'_>,
    declaration: &SourceDeclaration,
    rust_name: RustName,
    alias: &SourceTypeAlias,
) -> GenerationResult<RustTypeAlias> {
    Ok(RustTypeAlias {
        declaration: declaration.id,
        rust_name,
        target: lower_type(context, declaration.id, "type_alias.target", &alias.target)?,
        source: SourceDeclarationMetadata::from_source(declaration),
    })
}

fn lower_variable(
    context: &LoweringContext<'_>,
    declaration: &SourceDeclaration,
    rust_name: RustName,
    variable: &SourceVariable,
) -> GenerationResult<RustVariable> {
    let mutability = variable_mutability(declaration.id, variable)?;
    Ok(RustVariable {
        declaration: declaration.id,
        rust_name,
        link_name: variable.link_name.clone(),
        ty: lower_type(context, declaration.id, "variable.type", &variable.ty)?,
        mutability,
        thread_local: false,
        symbol: native_symbol_binding(context, declaration.id)?,
        source: SourceDeclarationMetadata::from_source(declaration),
    })
}

fn variable_mutability(
    declaration: DeclarationId,
    variable: &SourceVariable,
) -> GenerationResult<RustVariableMutability> {
    if variable.thread_local {
        return Err(GenerationError::UnsupportedDeclaration {
            declaration,
            reason: "thread-local extern statics are explicitly rejected",
        });
    }
    Ok(if variable.ty.qualifiers.is_const {
        RustVariableMutability::ReadOnly
    } else {
        RustVariableMutability::Mutable
    })
}

fn lower_macro(
    source: &SourceMacro,
    global_names: &mut NameAllocator,
    diagnostics: &mut Vec<GenerationDiagnostic>,
    context: GenerationContext,
) -> GenerationResult<RustMacro> {
    let emitted = source.support.is_supported()
        && source.form == MacroForm::ObjectLike
        && source.category != MacroCategory::Unsupported
        && matches!(source.value, Some(MacroValue::Integer { .. }));
    if !emitted {
        diagnostics.push(GenerationDiagnostic::preserved_macro_not_emitted(
            context, source.id,
        ));
    }
    Ok(RustMacro {
        macro_id: source.id,
        identity_file: source.identity_file,
        rust_name: global_names.local_name(Some(&source.name), "macro", source.id.as_bytes())?,
        source_name: source.name.clone(),
        form: source.form,
        category: source.category,
        body: source.body.clone(),
        normalized_tokens: source.normalized_tokens.clone(),
        value: source.value.clone(),
        occurrences: source.occurrences.clone(),
        support: source.support.clone(),
        emitted,
    })
}

fn native_symbol_binding(
    context: &LoweringContext<'_>,
    declaration: DeclarationId,
) -> GenerationResult<NativeSymbolBinding> {
    let source_declaration = context
        .source
        .source()
        .declaration(declaration)
        .ok_or(GenerationError::MissingDeclaration { declaration })?;
    let link_name = match &source_declaration.kind {
        SourceDeclarationKind::Function(function) => function.link_name.as_str(),
        SourceDeclarationKind::Variable(variable) => variable.link_name.as_str(),
        _ => {
            return Err(GenerationError::UnsupportedDeclaration {
                declaration,
                reason: "native symbol binding requested for a non-symbol declaration",
            });
        }
    };
    let evidence = context.declaration_evidence(declaration)?;
    let (provider, artifact_fingerprint) = match evidence.provider() {
        ProviderAssessment::Resolved {
            provider,
            artifact_fingerprint,
        } => (*provider, *artifact_fingerprint),
        _ => {
            return Err(GenerationError::UnsupportedDeclaration {
                declaration,
                reason: "external declaration lacks one resolved provider",
            });
        }
    };
    let (symbol_reference, expected_name, actual_name, decoration) = match evidence.symbol() {
        SymbolAssessment::Exact {
            symbol,
            expected_name,
            actual_name,
            decoration,
            ..
        } if symbol.provider() == provider => (symbol, expected_name, actual_name, decoration),
        _ => {
            return Err(GenerationError::UnsupportedDeclaration {
                declaration,
                reason: "external declaration lacks one exact symbol identity",
            });
        }
    };
    validate_emittable_symbol_name(
        declaration,
        link_name,
        expected_name,
        actual_name,
        decoration,
    )?;
    let inventory = context
        .evidence
        .package()
        .inventories()
        .iter()
        .find(|inventory| inventory.artifact().provider_id() == provider)
        .ok_or(GenerationError::UnsupportedDeclaration {
            declaration,
            reason: "resolved provider inventory is absent",
        })?;
    let symbol = inventory.symbol(symbol_reference.symbol()).ok_or(
        GenerationError::UnsupportedDeclaration {
            declaration,
            reason: "exact symbol identity is absent from its provider inventory",
        },
    )?;
    if symbol.raw_name() != link_name.as_bytes() {
        return Err(GenerationError::UnsupportedDeclaration {
            declaration,
            reason: "undecorated symbol bytes differ from the emitted PARC link name",
        });
    }
    Ok(NativeSymbolBinding {
        provider,
        artifact_fingerprint,
        artifact_path: inventory.artifact().canonical_path().to_path_buf(),
        symbol: symbol.id(),
        expected_name: expected_name.clone(),
        actual_name: actual_name.clone(),
        raw_name: symbol.raw_name().to_vec(),
        decoration: decoration.clone(),
    })
}

fn validate_emittable_symbol_name(
    declaration: DeclarationId,
    link_name: &str,
    expected_name: &str,
    actual_name: &str,
    decoration: &linc::contract::SymbolDecoration,
) -> GenerationResult<()> {
    if link_name.is_empty() || link_name.chars().any(char::is_control) {
        return Err(GenerationError::UnsupportedDeclaration {
            declaration,
            reason: "native link names must be nonempty and contain no control characters",
        });
    }
    if link_name != expected_name || expected_name != actual_name {
        return Err(GenerationError::UnsupportedDeclaration {
            declaration,
            reason: "emission requires identical PARC, expected, and actual symbol names",
        });
    }
    if !matches!(decoration, linc::contract::SymbolDecoration::None) {
        return Err(GenerationError::UnsupportedDeclaration {
            declaration,
            reason: "decorated, versioned, or otherwise transformed symbols are not frozen",
        });
    }
    Ok(())
}

fn lower_type(
    context: &LoweringContext<'_>,
    declaration: DeclarationId,
    path: &str,
    ty: &CType,
) -> GenerationResult<RustType> {
    validate_type_semantics(declaration, path, ty)?;
    let kind = match &ty.kind {
        CTypeKind::Void => RustTypeKind::Void,
        CTypeKind::Bool => {
            let layout = context.source.source().target().c_data_model().bool_layout;
            if layout.storage_bits != 8 || layout.alignment_bits != 8 {
                return unsupported_type(
                    declaration,
                    path,
                    "target C _Bool is not an 8-bit scalar",
                );
            }
            RustTypeKind::Scalar(RustScalar::Bool)
        }
        CTypeKind::Integer(integer) => RustTypeKind::Scalar(lower_integer(
            declaration,
            path,
            integer,
            context.source.source().target().c_data_model(),
        )?),
        CTypeKind::Floating(floating) => RustTypeKind::Scalar(lower_float(
            declaration,
            path,
            floating,
            context.source.source().target().c_data_model(),
        )?),
        CTypeKind::Complex(_) => {
            return unsupported_type(declaration, path, "complex C representation is not frozen");
        }
        CTypeKind::Pointer(pointee) => match &pointee.kind {
            CTypeKind::Function(function) => {
                validate_type_semantics(declaration, &format!("{path}.pointee"), pointee)?;
                lower_function_pointer(context, declaration, path, function)?
            }
            _ => RustTypeKind::Pointer(Box::new(lower_type(
                context,
                declaration,
                &format!("{path}.pointee"),
                pointee,
            )?)),
        },
        CTypeKind::Array {
            element,
            bound: ArrayBound::Fixed { elements },
            parameter_qualifiers,
        } if *parameter_qualifiers == TypeQualifiers::NONE && *elements != 0 => {
            let (size_bits, _) = abi_size_alignment(context, declaration, path, ty, 0)?;
            if !rust_object_size_fits(context.source.source().target().pointer_width(), size_bits) {
                return unsupported_type(
                    declaration,
                    path,
                    "array exceeds Rust's target object-size limit",
                );
            }
            RustTypeKind::FixedArray {
                element: Box::new(lower_type(
                    context,
                    declaration,
                    &format!("{path}.element"),
                    element,
                )?),
                elements: *elements,
            }
        }
        CTypeKind::Array { .. } => {
            return unsupported_type(
                declaration,
                path,
                "only nonzero fixed arrays without parameter-only qualifiers are frozen",
            );
        }
        CTypeKind::Function(_) => {
            return unsupported_type(
                declaration,
                path,
                "bare C function types require an explicit pointer projection",
            );
        }
        CTypeKind::AliasRef(target) | CTypeKind::RecordRef(target) | CTypeKind::EnumRef(target) => {
            RustTypeKind::Named {
                declaration: *target,
                rust_name: context.name(*target)?,
            }
        }
        CTypeKind::Unsupported { .. } => {
            return unsupported_type(declaration, path, "PARC retained an unsupported type node");
        }
    };
    Ok(RustType {
        qualifiers: ty.qualifiers,
        nullability: ty.nullability,
        support: ty.support.clone(),
        kind,
    })
}

fn lower_function_pointer(
    context: &LoweringContext<'_>,
    declaration: DeclarationId,
    path: &str,
    function: &parc::contract::CFunctionType,
) -> GenerationResult<RustTypeKind> {
    let abi = lower_calling_convention(
        declaration,
        &function.calling_convention,
        context.source.source().target().architecture(),
        context.source.source().target().operating_system(),
    )?;
    if !matches!(
        function.prototype,
        FunctionPrototype::Prototyped { variadic: false }
    ) {
        return unsupported_type(
            declaration,
            path,
            "variadic or unspecified function pointers are not frozen",
        );
    }
    let parameters = function
        .parameters
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            let parameter_path = format!("{path}.parameters[{index}]");
            lower_parameter_type(context, declaration, &parameter_path, &parameter.ty)
        })
        .collect::<GenerationResult<Vec<_>>>()?;
    Ok(RustTypeKind::FunctionPointer {
        abi,
        parameters,
        return_type: Box::new(lower_type(
            context,
            declaration,
            &format!("{path}.return_type"),
            &function.return_type,
        )?),
        variadic: false,
    })
}

fn validate_type_semantics(
    declaration: DeclarationId,
    path: &str,
    ty: &CType,
) -> GenerationResult<()> {
    if ty.qualifiers.is_atomic {
        return unsupported_type(declaration, path, "_Atomic semantics are not modeled");
    }
    if ty.qualifiers.is_volatile {
        return unsupported_type(
            declaration,
            path,
            "volatile access semantics are not modeled",
        );
    }
    if ty.nullability != Nullability::Unspecified
        && !matches!(ty.kind, CTypeKind::Pointer(_) | CTypeKind::Function(_))
    {
        return unsupported_type(
            declaration,
            path,
            "nullability is only meaningful on pointer-like types",
        );
    }
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ParameterAliasError {
    InvalidTarget,
    Cycle,
    Depth,
}

fn parameter_requires_c_adjustment(
    context: &LoweringContext<'_>,
    declaration: DeclarationId,
    path: &str,
    ty: &CType,
) -> GenerationResult<bool> {
    requires_c_parameter_adjustment(ty, |target| {
        context
            .source
            .source()
            .declaration(target)
            .and_then(|declaration| match &declaration.kind {
                SourceDeclarationKind::TypeAlias(alias) => Some(&alias.target),
                _ => None,
            })
    })
    .map_err(|error| GenerationError::UnsupportedType {
        declaration,
        path: path.to_owned(),
        reason: match error {
            ParameterAliasError::InvalidTarget => {
                "parameter AliasRef does not resolve to a type alias"
            }
            ParameterAliasError::Cycle => "parameter type alias chain is cyclic",
            ParameterAliasError::Depth => "parameter type alias chain exceeds 64 levels",
        },
    })
}

fn lower_parameter_type(
    context: &LoweringContext<'_>,
    declaration: DeclarationId,
    path: &str,
    ty: &CType,
) -> GenerationResult<RustType> {
    if !parameter_requires_c_adjustment(context, declaration, path, ty)? {
        return lower_type(context, declaration, path, ty);
    }
    let mut aliases = BTreeSet::new();
    lower_adjusted_parameter_type(context, declaration, path, ty, &mut aliases)
}

fn lower_adjusted_parameter_type(
    context: &LoweringContext<'_>,
    declaration: DeclarationId,
    path: &str,
    ty: &CType,
    aliases: &mut BTreeSet<DeclarationId>,
) -> GenerationResult<RustType> {
    validate_type_semantics(declaration, path, ty)?;
    let kind = match &ty.kind {
        CTypeKind::AliasRef(target) => {
            if !aliases.insert(*target) {
                return unsupported_type(declaration, path, "parameter type alias chain is cyclic");
            }
            let target_declaration = context.source.source().declaration(*target).ok_or(
                GenerationError::MissingDeclaration {
                    declaration: *target,
                },
            )?;
            let SourceDeclarationKind::TypeAlias(alias) = &target_declaration.kind else {
                return unsupported_type(
                    declaration,
                    path,
                    "parameter AliasRef does not resolve to a type alias",
                );
            };
            let lowered = lower_adjusted_parameter_type(
                context,
                declaration,
                &format!("{path}.alias_target"),
                &alias.target,
                aliases,
            );
            aliases.remove(target);
            return lowered;
        }
        CTypeKind::Array { element, bound, .. } => {
            if matches!(
                bound,
                ArrayBound::Variable { .. } | ArrayBound::Invalid { .. }
            ) {
                return unsupported_type(
                    declaration,
                    path,
                    "variable or invalid parameter array bound is not certified",
                );
            }
            RustTypeKind::Pointer(Box::new(lower_type(
                context,
                declaration,
                &format!("{path}.adjusted_pointee"),
                element,
            )?))
        }
        CTypeKind::Function(function) => {
            lower_function_pointer(context, declaration, path, function)?
        }
        _ => return lower_type(context, declaration, path, ty),
    };
    Ok(RustType {
        qualifiers: ty.qualifiers,
        nullability: ty.nullability,
        support: ty.support.clone(),
        kind,
    })
}

fn requires_c_parameter_adjustment<'a>(
    ty: &'a CType,
    mut resolve_alias: impl FnMut(DeclarationId) -> Option<&'a CType>,
) -> Result<bool, ParameterAliasError> {
    let mut current = ty;
    let mut aliases = BTreeSet::new();
    for _ in 0..=64 {
        match &current.kind {
            CTypeKind::Array { .. } | CTypeKind::Function(_) => return Ok(true),
            CTypeKind::AliasRef(target) => {
                if !aliases.insert(*target) {
                    return Err(ParameterAliasError::Cycle);
                }
                current = resolve_alias(*target).ok_or(ParameterAliasError::InvalidTarget)?;
            }
            _ => return Ok(false),
        }
    }
    Err(ParameterAliasError::Depth)
}

fn lower_integer(
    declaration: DeclarationId,
    path: &str,
    integer: &CIntegerType,
    model: &CDataModel,
) -> GenerationResult<RustScalar> {
    let signedness = match integer {
        CIntegerType::Char { signedness } => match signedness {
            CharTypeSignedness::Plain => match model.char_signedness {
                CharSignedness::Signed => Signedness::Signed,
                CharSignedness::Unsigned => Signedness::Unsigned,
            },
            CharTypeSignedness::Signed => Signedness::Signed,
            CharTypeSignedness::Unsigned => Signedness::Unsigned,
        },
        CIntegerType::Short { signedness }
        | CIntegerType::Int { signedness }
        | CIntegerType::Long { signedness }
        | CIntegerType::LongLong { signedness } => *signedness,
        CIntegerType::Int128 { .. } => {
            return unsupported_type(declaration, path, "128-bit C integers are not frozen");
        }
        CIntegerType::BitInt { .. } => {
            return unsupported_type(declaration, path, "_BitInt is not frozen");
        }
    };
    if signedness == Signedness::Signed
        && model.signed_integer_representation != SignedIntegerRepresentation::TwosComplement
    {
        return unsupported_type(
            declaration,
            path,
            "Rust signed integers require two's-complement target representation",
        );
    }
    let scalar = match integer {
        CIntegerType::Char {
            signedness: CharTypeSignedness::Plain,
        } => RustScalar::CChar {
            storage_bits: model.char_layout.storage_bits,
            alignment_bits: model.char_layout.alignment_bits,
        },
        CIntegerType::Char {
            signedness: CharTypeSignedness::Signed,
        } => RustScalar::CSignedChar {
            storage_bits: model.char_layout.storage_bits,
            alignment_bits: model.char_layout.alignment_bits,
        },
        CIntegerType::Char {
            signedness: CharTypeSignedness::Unsigned,
        } => RustScalar::CUnsignedChar {
            storage_bits: model.char_layout.storage_bits,
            alignment_bits: model.char_layout.alignment_bits,
        },
        CIntegerType::Short {
            signedness: Signedness::Signed,
        } => RustScalar::CShort {
            storage_bits: model.short_layout.storage_bits,
            alignment_bits: model.short_layout.alignment_bits,
        },
        CIntegerType::Short {
            signedness: Signedness::Unsigned,
        } => RustScalar::CUnsignedShort {
            storage_bits: model.short_layout.storage_bits,
            alignment_bits: model.short_layout.alignment_bits,
        },
        CIntegerType::Int {
            signedness: Signedness::Signed,
        } => RustScalar::CInt {
            storage_bits: model.int_layout.storage_bits,
            alignment_bits: model.int_layout.alignment_bits,
        },
        CIntegerType::Int {
            signedness: Signedness::Unsigned,
        } => RustScalar::CUnsignedInt {
            storage_bits: model.int_layout.storage_bits,
            alignment_bits: model.int_layout.alignment_bits,
        },
        CIntegerType::Long {
            signedness: Signedness::Signed,
        } => RustScalar::CLong {
            storage_bits: model.long_layout.storage_bits,
            alignment_bits: model.long_layout.alignment_bits,
        },
        CIntegerType::Long {
            signedness: Signedness::Unsigned,
        } => RustScalar::CUnsignedLong {
            storage_bits: model.long_layout.storage_bits,
            alignment_bits: model.long_layout.alignment_bits,
        },
        CIntegerType::LongLong {
            signedness: Signedness::Signed,
        } => RustScalar::CLongLong {
            storage_bits: model.long_long_layout.storage_bits,
            alignment_bits: model.long_long_layout.alignment_bits,
        },
        CIntegerType::LongLong {
            signedness: Signedness::Unsigned,
        } => RustScalar::CUnsignedLongLong {
            storage_bits: model.long_long_layout.storage_bits,
            alignment_bits: model.long_long_layout.alignment_bits,
        },
        CIntegerType::Int128 { .. } | CIntegerType::BitInt { .. } => {
            unreachable!("unsupported integer ranks returned above")
        }
    };
    if scalar.size_bits() == 0 || scalar.alignment_bits() == Some(0) {
        return unsupported_type(
            declaration,
            path,
            "C integer rank has an invalid target layout",
        );
    }
    Ok(scalar)
}

fn lower_float(
    declaration: DeclarationId,
    path: &str,
    floating: &CFloatingType,
    model: &CDataModel,
) -> GenerationResult<RustScalar> {
    match floating {
        CFloatingType::Float
            if model.float_layout.scalar.storage_bits == 32
                && model.float_layout.format == FloatingFormat::IeeeBinary32 =>
        {
            Ok(RustScalar::CFloat {
                storage_bits: model.float_layout.scalar.storage_bits,
                alignment_bits: model.float_layout.scalar.alignment_bits,
            })
        }
        CFloatingType::Double
            if model.double_layout.scalar.storage_bits == 64
                && model.double_layout.format == FloatingFormat::IeeeBinary64 =>
        {
            Ok(RustScalar::CDouble {
                storage_bits: model.double_layout.scalar.storage_bits,
                alignment_bits: model.double_layout.scalar.alignment_bits,
            })
        }
        CFloatingType::Float | CFloatingType::Double => unsupported_type(
            declaration,
            path,
            "target floating representation does not match a Rust scalar",
        ),
        CFloatingType::LongDouble | CFloatingType::Float128 | CFloatingType::Ts18661 { .. } => {
            unsupported_type(
                declaration,
                path,
                "extended floating representation is not frozen",
            )
        }
    }
}

pub(crate) fn lower_calling_convention(
    declaration: DeclarationId,
    convention: &CallingConvention,
    architecture: Architecture,
    operating_system: OperatingSystem,
) -> GenerationResult<RustAbi> {
    let supported = match convention {
        CallingConvention::C => Some(RustAbi::C),
        CallingConvention::Cdecl if architecture == Architecture::X86 => Some(RustAbi::Cdecl),
        CallingConvention::Stdcall
            if architecture == Architecture::X86
                && operating_system == OperatingSystem::Windows =>
        {
            Some(RustAbi::Stdcall)
        }
        CallingConvention::Fastcall
            if architecture == Architecture::X86
                && operating_system == OperatingSystem::Windows =>
        {
            Some(RustAbi::Fastcall)
        }
        CallingConvention::Thiscall
            if architecture == Architecture::X86
                && operating_system == OperatingSystem::Windows =>
        {
            Some(RustAbi::Thiscall)
        }
        CallingConvention::SysV64
            if architecture == Architecture::X86_64
                && operating_system != OperatingSystem::Windows =>
        {
            Some(RustAbi::SysV64)
        }
        CallingConvention::Win64
            if architecture == Architecture::X86_64
                && operating_system == OperatingSystem::Windows =>
        {
            Some(RustAbi::Win64)
        }
        CallingConvention::Aapcs
            if matches!(architecture, Architecture::Arm | Architecture::Aarch64) =>
        {
            Some(RustAbi::Aapcs)
        }
        _ => None,
    };
    supported.ok_or_else(|| GenerationError::UnsupportedCallingConvention {
        declaration,
        convention: convention.clone(),
        operating_system,
    })
}

fn abi_size_alignment(
    context: &LoweringContext<'_>,
    declaration: DeclarationId,
    path: &str,
    ty: &CType,
    depth: usize,
) -> GenerationResult<(u64, u64)> {
    if depth > 64 {
        return unsupported_type(declaration, path, "type layout recursion exceeds 64 levels");
    }
    validate_type_semantics(declaration, path, ty)?;
    let model = context.source.source().target().c_data_model();
    match &ty.kind {
        CTypeKind::Void | CTypeKind::Function(_) => {
            unsupported_type(declaration, path, "unsized type appears by value")
        }
        CTypeKind::Bool => Ok((
            u64::from(model.bool_layout.storage_bits),
            u64::from(model.bool_layout.alignment_bits),
        )),
        CTypeKind::Integer(integer) => {
            let scalar = lower_integer(declaration, path, integer, model)?;
            let alignment = integer_alignment(model, integer);
            Ok((scalar.size_bits(), u64::from(alignment)))
        }
        CTypeKind::Floating(floating) => {
            let scalar = lower_float(declaration, path, floating, model)?;
            let alignment = match floating {
                CFloatingType::Float => model.float_layout.scalar.alignment_bits,
                CFloatingType::Double => model.double_layout.scalar.alignment_bits,
                _ => unreachable!("extended floats were rejected by lower_float"),
            };
            Ok((scalar.size_bits(), u64::from(alignment)))
        }
        CTypeKind::Complex(_) => unsupported_type(declaration, path, "complex type is unsized"),
        CTypeKind::Pointer(_) => Ok((
            u64::from(model.pointer_layout.storage_bits),
            u64::from(model.pointer_layout.alignment_bits),
        )),
        CTypeKind::Array {
            element,
            bound: ArrayBound::Fixed { elements },
            parameter_qualifiers,
        } if *elements != 0 && *parameter_qualifiers == TypeQualifiers::NONE => {
            let (element_size, alignment) = abi_size_alignment(
                context,
                declaration,
                &format!("{path}.element"),
                element,
                depth + 1,
            )?;
            let size =
                element_size
                    .checked_mul(*elements)
                    .ok_or(GenerationError::LayoutMismatch {
                        declaration,
                        reason: "array size overflowed",
                    })?;
            if !rust_object_size_fits(context.source.source().target().pointer_width(), size) {
                return unsupported_type(
                    declaration,
                    path,
                    "array exceeds Rust's target object-size limit",
                );
            }
            Ok((size, alignment))
        }
        CTypeKind::Array { .. } => unsupported_type(
            declaration,
            path,
            "array bound has no frozen by-value representation",
        ),
        CTypeKind::AliasRef(target) => {
            let target_declaration = context.source.source().declaration(*target).ok_or(
                GenerationError::MissingDeclaration {
                    declaration: *target,
                },
            )?;
            match &target_declaration.kind {
                SourceDeclarationKind::TypeAlias(alias) => abi_size_alignment(
                    context,
                    declaration,
                    &format!("{path}.alias_target"),
                    &alias.target,
                    depth + 1,
                ),
                _ => Err(GenerationError::LayoutMismatch {
                    declaration,
                    reason: "AliasRef does not reference a type alias declaration",
                }),
            }
        }
        CTypeKind::RecordRef(target) => match context.layout(*target)? {
            LayoutEvidence::Record(layout) => {
                Ok((layout.size_bits(), u64::from(layout.alignment_bits())))
            }
            LayoutEvidence::Enum(_) => Err(GenerationError::LayoutMismatch {
                declaration,
                reason: "RecordRef references enum layout",
            }),
        },
        CTypeKind::EnumRef(target) => match context.layout(*target)? {
            LayoutEvidence::Enum(layout) => {
                Ok((layout.storage_bits(), u64::from(layout.alignment_bits())))
            }
            LayoutEvidence::Record(_) => Err(GenerationError::LayoutMismatch {
                declaration,
                reason: "EnumRef references record layout",
            }),
        },
        CTypeKind::Unsupported { .. } => {
            unsupported_type(declaration, path, "PARC retained an unsupported type node")
        }
    }
}

fn integer_alignment(model: &CDataModel, integer: &CIntegerType) -> u16 {
    match integer {
        CIntegerType::Char { .. } => model.char_layout.alignment_bits,
        CIntegerType::Short { .. } => model.short_layout.alignment_bits,
        CIntegerType::Int { .. } => model.int_layout.alignment_bits,
        CIntegerType::Long { .. } => model.long_layout.alignment_bits,
        CIntegerType::LongLong { .. } => model.long_long_layout.alignment_bits,
        CIntegerType::Int128 { .. } => model
            .int128_layout
            .map_or(0, |layout| layout.alignment_bits),
        CIntegerType::BitInt { .. } => 0,
    }
}

fn enum_storage(
    declaration: DeclarationId,
    layout: &EnumLayoutEvidence,
) -> GenerationResult<RustScalar> {
    scalar_for(layout.storage_bits() as u16, layout.signedness()).ok_or(
        GenerationError::InvalidEnumRepresentation {
            declaration,
            reason: "enum storage width has no frozen Rust scalar",
        },
    )
}

fn scalar_for(bits: u16, signedness: Signedness) -> Option<RustScalar> {
    match (bits, signedness) {
        (8, Signedness::Signed) => Some(RustScalar::I8),
        (8, Signedness::Unsigned) => Some(RustScalar::U8),
        (16, Signedness::Signed) => Some(RustScalar::I16),
        (16, Signedness::Unsigned) => Some(RustScalar::U16),
        (32, Signedness::Signed) => Some(RustScalar::I32),
        (32, Signedness::Unsigned) => Some(RustScalar::U32),
        (64, Signedness::Signed) => Some(RustScalar::I64),
        (64, Signedness::Unsigned) => Some(RustScalar::U64),
        _ => None,
    }
}

fn scalar_integer_compatible(source: RustScalar, measured: RustScalar) -> bool {
    source.size_bits() == measured.size_bits()
        && scalar_signedness(source).is_some()
        && scalar_signedness(source) == scalar_signedness(measured)
}

fn scalar_signedness(scalar: RustScalar) -> Option<Signedness> {
    match scalar {
        RustScalar::CChar { .. } => None,
        RustScalar::CSignedChar { .. }
        | RustScalar::CShort { .. }
        | RustScalar::CInt { .. }
        | RustScalar::CLong { .. }
        | RustScalar::CLongLong { .. }
        | RustScalar::I8
        | RustScalar::I16
        | RustScalar::I32
        | RustScalar::I64 => Some(Signedness::Signed),
        RustScalar::CUnsignedChar { .. }
        | RustScalar::CUnsignedShort { .. }
        | RustScalar::CUnsignedInt { .. }
        | RustScalar::CUnsignedLong { .. }
        | RustScalar::CUnsignedLongLong { .. }
        | RustScalar::U8
        | RustScalar::U16
        | RustScalar::U32
        | RustScalar::U64 => Some(Signedness::Unsigned),
        RustScalar::Bool
        | RustScalar::CFloat { .. }
        | RustScalar::CDouble { .. }
        | RustScalar::F32
        | RustScalar::F64 => None,
    }
}

fn integer_fits(value: ExactInteger, storage: RustScalar) -> bool {
    let bits = storage.size_bits();
    match storage {
        RustScalar::CSignedChar { .. }
        | RustScalar::CShort { .. }
        | RustScalar::CInt { .. }
        | RustScalar::CLong { .. }
        | RustScalar::CLongLong { .. }
        | RustScalar::I8
        | RustScalar::I16
        | RustScalar::I32
        | RustScalar::I64 => {
            let maximum = (1_i128 << (bits - 1)) - 1;
            let minimum = -(1_i128 << (bits - 1));
            match value {
                ExactInteger::Signed { value } => (minimum..=maximum).contains(&value),
                ExactInteger::Unsigned { value } => value <= maximum as u128,
            }
        }
        RustScalar::CUnsignedChar { .. }
        | RustScalar::CUnsignedShort { .. }
        | RustScalar::CUnsignedInt { .. }
        | RustScalar::CUnsignedLong { .. }
        | RustScalar::CUnsignedLongLong { .. }
        | RustScalar::U8
        | RustScalar::U16
        | RustScalar::U32
        | RustScalar::U64 => {
            let maximum = (1_u128 << bits) - 1;
            match value {
                ExactInteger::Signed { value } => value >= 0 && (value as u128) <= maximum,
                ExactInteger::Unsigned { value } => value <= maximum,
            }
        }
        RustScalar::Bool
        | RustScalar::CChar { .. }
        | RustScalar::CFloat { .. }
        | RustScalar::CDouble { .. }
        | RustScalar::F32
        | RustScalar::F64 => false,
    }
}

fn align_up(value: u64, alignment: u64) -> Option<u64> {
    if alignment == 0 || !alignment.is_power_of_two() {
        return None;
    }
    value
        .checked_add(alignment - 1)
        .map(|value| value & !(alignment - 1))
}

fn rust_object_size_fits(pointer_width: u16, size_bits: u64) -> bool {
    if !size_bits.is_multiple_of(8) || pointer_width == 0 || pointer_width > 128 {
        return false;
    }
    let maximum_bytes = if pointer_width == 128 {
        i128::MAX as u128
    } else {
        (1_u128 << (pointer_width - 1)) - 1
    };
    u128::from(size_bits / 8) <= maximum_bytes
}

fn unsupported_type<T>(
    declaration: DeclarationId,
    path: &str,
    reason: &'static str,
) -> GenerationResult<T> {
    Err(GenerationError::UnsupportedType {
        declaration,
        path: path.to_owned(),
        reason,
    })
}

#[derive(Default)]
struct NameAllocator {
    used: BTreeSet<String>,
}

impl NameAllocator {
    fn declaration_name(&mut self, declaration: &SourceDeclaration) -> GenerationResult<RustName> {
        self.local_name(
            declaration
                .name
                .as_ref()
                .map(|name| name.normalized.as_str()),
            "declaration",
            declaration.id.as_bytes(),
        )
        .map_err(|_| GenerationError::InvalidIdentifier {
            declaration: declaration.id,
        })
    }

    fn local_name(
        &mut self,
        source_name: Option<&str>,
        role: &str,
        identity: &[u8; 32],
    ) -> GenerationResult<RustName> {
        let mut base = source_name
            .filter(|name| !name.is_empty())
            .map(sanitize_identifier)
            .unwrap_or_else(|| format!("__gerc_{role}_{}", identity_hex(identity)));
        if is_unrawable_keyword(&base) {
            base = format!("__gerc_{base}");
        }
        let mut candidate = escape_keyword(base.clone());
        if !self.used.insert(candidate.clone()) {
            candidate = escape_keyword(format!("{base}_{}", identity_hex(identity)));
            if !self.used.insert(candidate.clone()) {
                return Err(GenerationError::ProjectionInvariant {
                    reason: "identifier allocation collision survived its identity suffix",
                });
            }
        }
        RustName::checked(candidate).ok_or(GenerationError::ProjectionInvariant {
            reason: "identifier allocator produced an invalid name",
        })
    }
}

fn sanitize_identifier(value: &str) -> String {
    let mut output = String::new();
    for (index, byte) in value.bytes().enumerate() {
        let valid = if index == 0 {
            byte == b'_' || byte.is_ascii_alphabetic()
        } else {
            byte == b'_' || byte.is_ascii_alphanumeric()
        };
        if valid {
            output.push(char::from(byte));
        } else {
            use std::fmt::Write as _;
            write!(output, "_u{byte:02x}").expect("writing into a String cannot fail");
        }
    }
    if output.is_empty() {
        output.push_str("__gerc_unnamed");
    }
    output
}

fn escape_keyword(value: String) -> String {
    if is_keyword(&value) {
        format!("r#{value}")
    } else {
        value
    }
}

fn is_unrawable_keyword(value: &str) -> bool {
    matches!(value, "_" | "crate" | "self" | "Self" | "super")
}

fn is_keyword(value: &str) -> bool {
    matches!(
        value,
        "as" | "async"
            | "await"
            | "abstract"
            | "become"
            | "box"
            | "break"
            | "const"
            | "continue"
            | "crate"
            | "dyn"
            | "do"
            | "else"
            | "enum"
            | "extern"
            | "false"
            | "final"
            | "fn"
            | "for"
            | "gen"
            | "if"
            | "impl"
            | "in"
            | "let"
            | "loop"
            | "macro"
            | "match"
            | "mod"
            | "move"
            | "mut"
            | "override"
            | "priv"
            | "pub"
            | "ref"
            | "return"
            | "static"
            | "struct"
            | "trait"
            | "true"
            | "try"
            | "type"
            | "typeof"
            | "unsafe"
            | "unsized"
            | "use"
            | "union"
            | "virtual"
            | "where"
            | "while"
            | "yield"
    )
}

fn identity_hex(identity: &[u8; 32]) -> String {
    identity.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use std::{
        collections::BTreeMap,
        fs,
        process::Command,
        sync::atomic::{AtomicU64, Ordering},
    };

    use parc::contract::{
        Architecture, ArrayBound, CFunctionType, CType, CTypeKind, CallingConvention,
        DeclarationId, DeclarationIdentity, EntityNamespace, EntityScope, FunctionPrototype,
        Linkage, Nullability, OperatingSystem, SourceDeclaration, SourceDeclarationKind,
        SourceName, SourceTypeAlias, SourceVariable, SupportStatus, TypeQualifiers, Visibility,
    };

    use linc::contract::SymbolDecoration;

    use super::{
        infer_packing, lower_calling_convention, requires_c_parameter_adjustment,
        rust_object_size_fits, validate_emittable_symbol_name, variable_mutability, NameAllocator,
        RecordFieldShape,
    };
    use crate::{
        GenerationErrorCode, RustRecordKind, RustVariableMutability, SourceDeclarationMetadata,
    };

    static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

    #[test]
    fn every_strict_and_reserved_keyword_maps_to_compilable_rust() {
        let keywords = [
            "as", "break", "const", "continue", "crate", "else", "enum", "extern", "false", "fn",
            "for", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub", "ref",
            "return", "self", "Self", "static", "struct", "super", "trait", "true", "type",
            "unsafe", "use", "where", "while", "async", "await", "dyn", "abstract", "become",
            "box", "do", "final", "macro", "override", "priv", "typeof", "unsized", "virtual",
            "yield", "try", "gen", "union", "_",
        ];
        let mut allocator = NameAllocator::default();
        let mut source = String::from("#![no_std]\n");
        for (index, keyword) in keywords.into_iter().enumerate() {
            let mut identity = [0_u8; 32];
            identity[..8].copy_from_slice(&(index as u64).to_le_bytes());
            let name = allocator
                .local_name(Some(keyword), "keyword", &identity)
                .expect("keyword mapping");
            let original = format!("/*original spelling*/{keyword}");
            let declaration = SourceDeclaration {
                id: declaration_id(index as u8 + 10),
                identity: DeclarationIdentity::Named {
                    namespace: EntityNamespace::Ordinary,
                    scope: EntityScope::TranslationUnit,
                    normalized_name: keyword.to_owned(),
                },
                name: Some(SourceName {
                    normalized: keyword.to_owned(),
                    original: original.clone(),
                }),
                linkage: Linkage::None,
                visibility: Visibility::Unspecified,
                occurrences: Vec::new(),
                support: SupportStatus::Supported,
                kind: SourceDeclarationKind::TypeAlias(SourceTypeAlias {
                    target: CType {
                        qualifiers: TypeQualifiers::NONE,
                        nullability: Nullability::Unspecified,
                        kind: CTypeKind::Bool,
                        support: SupportStatus::Supported,
                    },
                }),
            };
            let metadata = SourceDeclarationMetadata::from_source(&declaration);
            assert_eq!(metadata.name().unwrap().normalized, keyword);
            assert_eq!(metadata.name().unwrap().original, original);
            source.push_str("pub fn ");
            source.push_str(name.as_str());
            source.push_str("() {}\n");
            if matches!(keyword, "_" | "crate" | "self" | "Self" | "super") {
                assert!(!name.as_str().starts_with("r#"));
            } else {
                assert!(name.as_str().starts_with("r#"));
            }
        }
        compile_rust(&source, "keyword_projection");
    }

    #[test]
    fn c_namespaces_and_post_normalization_collisions_remain_distinct() {
        let mut allocator = NameAllocator::default();
        let first = allocator
            .local_name(Some("same-name"), "ordinary", &[1; 32])
            .expect("first normalized name");
        let second = allocator
            .local_name(Some("same_u2dname"), "tag", &[2; 32])
            .expect("post-normalization collision");
        let third = allocator
            .local_name(Some("same-name"), "value", &[3; 32])
            .expect("C namespace collision");
        assert_eq!(first.as_str(), "same_u2dname");
        assert_ne!(first, second);
        assert_ne!(first, third);
        assert_ne!(second, third);
        let source = format!(
            "#![no_std]\npub struct {} {{ _x: u8 }}\npub type {} = u8;\npub const {}: u8 = 0;\n",
            first.as_str(),
            second.as_str(),
            third.as_str(),
        );
        compile_rust(&source, "namespace_collisions");
    }

    #[test]
    fn direct_and_aliased_array_or_function_parameters_are_never_emitted_by_value() {
        let scalar = CType {
            qualifiers: TypeQualifiers::NONE,
            nullability: Nullability::Unspecified,
            kind: CTypeKind::Bool,
            support: SupportStatus::Supported,
        };
        let array = CType {
            qualifiers: TypeQualifiers::NONE,
            nullability: Nullability::Unspecified,
            kind: CTypeKind::Array {
                element: Box::new(scalar),
                bound: ArrayBound::Fixed { elements: 4 },
                parameter_qualifiers: TypeQualifiers::NONE,
            },
            support: SupportStatus::Supported,
        };
        assert!(requires_c_parameter_adjustment(&array, |_| None).expect("direct array adjustment"));
        let function = CType {
            qualifiers: TypeQualifiers::NONE,
            nullability: Nullability::Unspecified,
            kind: CTypeKind::Function(CFunctionType {
                return_type: Box::new(CType {
                    qualifiers: TypeQualifiers::NONE,
                    nullability: Nullability::Unspecified,
                    kind: CTypeKind::Void,
                    support: SupportStatus::Supported,
                }),
                parameters: Vec::new(),
                prototype: FunctionPrototype::Prototyped { variadic: false },
                calling_convention: CallingConvention::C,
            }),
            support: SupportStatus::Supported,
        };
        assert!(requires_c_parameter_adjustment(&function, |_| None)
            .expect("direct function adjustment"));

        let array_alias = declaration_id(1);
        let function_alias = declaration_id(2);
        let chained_array_alias = declaration_id(4);
        let aliases = BTreeMap::from([
            (array_alias, array),
            (function_alias, function),
            (
                chained_array_alias,
                CType {
                    qualifiers: TypeQualifiers::NONE,
                    nullability: Nullability::Unspecified,
                    kind: CTypeKind::AliasRef(array_alias),
                    support: SupportStatus::Supported,
                },
            ),
        ]);
        for alias in [array_alias, function_alias, chained_array_alias] {
            let parameter = CType {
                qualifiers: TypeQualifiers::NONE,
                nullability: Nullability::Unspecified,
                kind: CTypeKind::AliasRef(alias),
                support: SupportStatus::Supported,
            };
            assert!(
                requires_c_parameter_adjustment(&parameter, |target| aliases.get(&target))
                    .expect("alias-mediated adjustment")
            );
        }
    }

    #[test]
    fn symbol_names_require_exact_undecorated_noncontrol_bytes() {
        let declaration = declaration_id(3);
        validate_emittable_symbol_name(
            declaration,
            "parc_open",
            "parc_open",
            "parc_open",
            &SymbolDecoration::None,
        )
        .expect("exact undecorated symbol");

        let control = validate_emittable_symbol_name(
            declaration,
            "parc\0open",
            "parc\0open",
            "parc\0open",
            &SymbolDecoration::None,
        )
        .expect_err("control name must reject");
        assert_eq!(control.code(), GenerationErrorCode::UnsupportedDeclaration);
        assert!(control.to_string().contains("control characters"));

        let versioned = validate_emittable_symbol_name(
            declaration,
            "parc_open",
            "parc_open",
            "parc_open",
            &SymbolDecoration::Versioned {
                version: b"GERC_1".to_vec(),
                is_default: false,
            },
        )
        .expect_err("versioned name must reject");
        assert_eq!(
            versioned.code(),
            GenerationErrorCode::UnsupportedDeclaration
        );
        assert!(versioned.to_string().contains("decorated"));

        let underscored = validate_emittable_symbol_name(
            declaration,
            "parc_open",
            "_parc_open",
            "_parc_open",
            &SymbolDecoration::LeadingUnderscore,
        )
        .expect_err("leading underscore must reject");
        assert_eq!(
            underscored.code(),
            GenerationErrorCode::UnsupportedDeclaration
        );
    }

    #[test]
    fn globals_preserve_constness_and_tls_fails_closed() {
        let declaration = declaration_id(8);
        let variable = |is_const, thread_local| SourceVariable {
            link_name: "h4_global".to_owned(),
            ty: CType {
                qualifiers: TypeQualifiers {
                    is_const,
                    ..TypeQualifiers::NONE
                },
                nullability: Nullability::Unspecified,
                kind: CTypeKind::Bool,
                support: SupportStatus::Supported,
            },
            thread_local,
        };
        assert_eq!(
            variable_mutability(declaration, &variable(true, false)).expect("const global"),
            RustVariableMutability::ReadOnly
        );
        assert_eq!(
            variable_mutability(declaration, &variable(false, false)).expect("mutable global"),
            RustVariableMutability::Mutable
        );
        let error =
            variable_mutability(declaration, &variable(false, true)).expect_err("TLS must reject");
        assert_eq!(error.code(), GenerationErrorCode::UnsupportedDeclaration);
        assert!(error.to_string().contains("thread-local"));
    }

    #[test]
    fn measured_natural_and_packed_record_layouts_have_exact_rust_representations() {
        let natural = [
            RecordFieldShape {
                offset_bits: 0,
                size_bits: 8,
                natural_alignment_bits: 8,
                measured_alignment_bits: Some(8),
            },
            RecordFieldShape {
                offset_bits: 32,
                size_bits: 32,
                natural_alignment_bits: 32,
                measured_alignment_bits: Some(32),
            },
        ];
        assert_eq!(
            infer_packing(RustRecordKind::Struct, &natural, 64, 32),
            Some(None)
        );

        let packed_one = [
            natural[0],
            RecordFieldShape {
                offset_bits: 8,
                ..natural[1]
            },
        ];
        assert_eq!(
            infer_packing(RustRecordKind::Struct, &packed_one, 40, 8),
            Some(Some(8))
        );

        let packed_two = [
            natural[0],
            RecordFieldShape {
                offset_bits: 16,
                measured_alignment_bits: Some(16),
                ..natural[1]
            },
        ];
        assert_eq!(
            infer_packing(RustRecordKind::Struct, &packed_two, 48, 16),
            Some(Some(16))
        );

        let packed_union = [
            RecordFieldShape {
                offset_bits: 0,
                size_bits: 32,
                natural_alignment_bits: 32,
                measured_alignment_bits: Some(32),
            },
            RecordFieldShape {
                offset_bits: 0,
                size_bits: 64,
                natural_alignment_bits: 64,
                measured_alignment_bits: Some(32),
            },
        ];
        assert_eq!(
            infer_packing(RustRecordKind::Union, &packed_union, 64, 32),
            Some(Some(32))
        );

        let unrepresentable = [
            natural[0],
            RecordFieldShape {
                offset_bits: 24,
                ..natural[1]
            },
        ];
        assert_eq!(
            infer_packing(RustRecordKind::Struct, &unrepresentable, 64, 32),
            None
        );
    }

    #[test]
    fn fixed_arrays_must_fit_rust_target_object_limits() {
        assert!(rust_object_size_fits(32, 8));
        assert!(rust_object_size_fits(32, (i32::MAX as u64) * 8));
        assert!(!rust_object_size_fits(32, (i32::MAX as u64 + 1) * 8));
        assert!(rust_object_size_fits(64, u64::MAX - 7));
        assert!(!rust_object_size_fits(64, u64::MAX));
    }

    #[test]
    fn experimental_vectorcall_is_rejected_even_on_windows_targets() {
        let error = lower_calling_convention(
            declaration_id(5),
            &CallingConvention::Vectorcall,
            Architecture::X86_64,
            OperatingSystem::Windows,
        )
        .expect_err("Rust 1.89 vectorcall ABI is experimental");
        assert_eq!(
            error.code(),
            GenerationErrorCode::UnsupportedCallingConvention
        );
    }

    fn declaration_id(value: u8) -> DeclarationId {
        format!("pdecl1_{value:064x}")
            .parse()
            .expect("test declaration ID")
    }

    fn compile_rust(source: &str, name: &str) {
        let nonce = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
        let directory =
            std::env::temp_dir().join(format!("gerc-{name}-{}-{nonce}", std::process::id()));
        fs::create_dir_all(&directory).expect("create compile-test directory");
        let input = directory.join("lib.rs");
        let output = directory.join("lib.rmeta");
        fs::write(&input, source).expect("write compile-test source");
        let rustc = std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
        let result = Command::new(rustc)
            .arg("--crate-name")
            .arg(name)
            .arg("--crate-type=lib")
            .arg("--edition=2024")
            .arg("--emit=metadata")
            .arg("-o")
            .arg(&output)
            .arg(&input)
            .output()
            .expect("run rustc");
        let _ = fs::remove_dir_all(&directory);
        assert!(
            result.status.success(),
            "generated Rust did not compile:\n{}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
}
