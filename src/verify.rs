use std::collections::{BTreeMap, BTreeSet};

use linc::contract::{LayoutEvidence, ProviderAssessment, SymbolAssessment, ValidatedLinkAnalysis};
use parc::contract::{
    ArrayBound, AttributeDisposition, CType, CTypeKind, ClosureRequirement, CompleteSourcePackage,
    DeclarationId, FunctionPrototype, RecordCompleteness, RecordKind, SourceDeclaration,
    SourceDeclarationKind, SupportStatus, TypeQualifiers,
};

use crate::{
    generate::lower_calling_convention, GenerationError, GenerationRequest, GenerationResult,
    RustItem, RustRecordKind, RustType, RustTypeKind, ValidatedRustProjection,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypePosition {
    ByValue,
    BehindPointer,
    Return,
    Parameter,
    /// The target of a type-alias *declaration*.
    ///
    /// A typedef is a name, not a use. `typedef struct T T;` does not use `T`
    /// by value -- it says what `T` means, and whether any use is by value is
    /// decided at that use, which `AliasRef` already carries the position for.
    ///
    /// Verifying the declaration at `ByValue` refused the single most common
    /// spelling of an opaque handle in C: `typedef struct sqlite3 sqlite3`,
    /// `typedef struct lua_State lua_State`. The bare `struct T;` form worked,
    /// which is why nothing noticed.
    AliasTarget,
}

/// Closed-world verification performed before name allocation or source
/// rendering. PARC and LINC wrappers prove their own contracts; this pass
/// proves the narrower set of invariants required by GERC's Rust ABI model.
pub(crate) fn verify_pre_lowering(request: &GenerationRequest<'_>) -> GenerationResult<()> {
    let verifier = SourceVerifier::new(request.source(), request.evidence(), request)?;
    verifier.verify()
}

struct SourceVerifier<'a> {
    source: &'a CompleteSourcePackage,
    evidence: &'a ValidatedLinkAnalysis,
    requirements: BTreeMap<DeclarationId, ClosureRequirement>,
}

impl<'a> SourceVerifier<'a> {
    fn new(
        source: &'a CompleteSourcePackage,
        evidence: &'a ValidatedLinkAnalysis,
        request: &GenerationRequest<'_>,
    ) -> GenerationResult<Self> {
        let package = evidence.package();
        if package.source_fingerprint() != source.source().fingerprint() {
            return Err(GenerationError::SourceFingerprintMismatch);
        }
        if package.target_fingerprint() != source.source().target_fingerprint() {
            return Err(GenerationError::TargetFingerprintMismatch);
        }
        let requirements = request
            .declaration_closure()
            .iter()
            .map(|entry| (entry.declaration(), entry.requirement()))
            .collect();
        Ok(Self {
            source,
            evidence,
            requirements,
        })
    }

    fn verify(&self) -> GenerationResult<()> {
        let mut declarations = BTreeSet::new();
        for declaration in self.requirements.keys().copied() {
            if !declarations.insert(declaration) {
                return Err(GenerationError::ProjectionInvariant {
                    reason: "closed source world repeats a DeclarationId",
                });
            }
            let source = self.declaration(declaration, declaration)?;
            self.verify_reconciled_declaration(source)?;
            self.verify_evidence(source)?;
        }

        for declaration in self.requirements.keys().copied() {
            let source = self.declaration(declaration, declaration)?;
            let mut aliases = Vec::new();
            let mut by_value_records = Vec::new();
            self.verify_declaration(source, &mut aliases, &mut by_value_records)?;
        }
        Ok(())
    }

    fn verify_reconciled_declaration(
        &self,
        declaration: &SourceDeclaration,
    ) -> GenerationResult<()> {
        if !declaration.support.is_supported() {
            return Err(GenerationError::UnsupportedDeclaration {
                declaration: declaration.id,
                reason: "PARC source support is not fully accepted",
            });
        }
        let mut occurrences = BTreeSet::new();
        for occurrence in &declaration.occurrences {
            if !occurrences.insert(occurrence.id) {
                return Err(GenerationError::UnsupportedDeclaration {
                    declaration: declaration.id,
                    reason: "reconciled declaration repeats a source occurrence",
                });
            }
            if occurrence.attributes.iter().any(|attribute| {
                attribute.disposition == AttributeDisposition::UnsupportedAbiRelevant
            }) {
                return Err(GenerationError::UnsupportedDeclaration {
                    declaration: declaration.id,
                    reason: "an ABI-relevant declaration attribute is unsupported",
                });
            }
        }
        Ok(())
    }

    fn verify_evidence(&self, declaration: &SourceDeclaration) -> GenerationResult<()> {
        let package = self.evidence.package();
        let evidence = package
            .declaration_evidence()
            .binary_search_by_key(&declaration.id, |entry| entry.declaration())
            .ok()
            .map(|index| &package.declaration_evidence()[index])
            .ok_or(GenerationError::MissingDeclarationEvidence {
                declaration: declaration.id,
            })?;
        if evidence.source_fingerprint() != self.source.source().fingerprint() {
            return Err(GenerationError::SourceFingerprintMismatch);
        }
        if evidence.target_fingerprint() != self.source.source().target_fingerprint() {
            return Err(GenerationError::TargetFingerprintMismatch);
        }
        if matches!(
            declaration.kind,
            SourceDeclarationKind::Function(_) | SourceDeclarationKind::Variable(_)
        ) && declaration.linkage == parc::contract::Linkage::External
        {
            let provider = match evidence.provider() {
                ProviderAssessment::Resolved { provider, .. } => *provider,
                _ => {
                    return Err(GenerationError::UnsupportedDeclaration {
                        declaration: declaration.id,
                        reason: "selected extern has no single resolved provider",
                    });
                }
            };
            if !matches!(evidence.symbol(), SymbolAssessment::Exact { symbol, .. } if symbol.provider() == provider)
            {
                return Err(GenerationError::UnsupportedDeclaration {
                    declaration: declaration.id,
                    reason: "selected extern has no exact provider-bound symbol",
                });
            }
            let in_plan = package
                .resolved_link_plan()
                .atoms()
                .iter()
                .filter_map(linc::contract::LinkAtom::artifact)
                .any(|artifact| artifact.provider_id() == provider);
            if !in_plan {
                return Err(GenerationError::UnsupportedDeclaration {
                    declaration: declaration.id,
                    reason: "selected extern provider is absent from the ordered link plan",
                });
            }
        }
        Ok(())
    }

    fn verify_declaration(
        &self,
        declaration: &SourceDeclaration,
        aliases: &mut Vec<DeclarationId>,
        by_value_records: &mut Vec<DeclarationId>,
    ) -> GenerationResult<()> {
        match &declaration.kind {
            SourceDeclarationKind::Function(function) => {
                lower_calling_convention(
                    declaration.id,
                    &function.calling_convention,
                    self.source.source().target().architecture(),
                    self.source.source().target().operating_system(),
                )?;
                if !matches!(
                    function.prototype,
                    FunctionPrototype::Prototyped { variadic: false }
                ) {
                    return self.unsupported_declaration(
                        declaration.id,
                        "variadic or unspecified function prototypes are outside the certified ABI",
                    );
                }
                self.verify_type(
                    declaration.id,
                    "function.return_type",
                    &function.return_type,
                    TypePosition::Return,
                    aliases,
                    by_value_records,
                )?;
                for parameter in &function.parameters {
                    self.verify_type(
                        declaration.id,
                        &format!("function.parameters[{}]", parameter.ordinal),
                        &parameter.ty,
                        TypePosition::Parameter,
                        aliases,
                        by_value_records,
                    )?;
                }
            }
            SourceDeclarationKind::Record(record) => {
                let requirement = self.requirement(declaration.id, declaration.id)?;
                if requirement == ClosureRequirement::Definition {
                    self.verify_record(declaration.id, record, aliases, by_value_records)?;
                }
            }
            SourceDeclarationKind::Enum(enumeration) => {
                self.require_layout(declaration.id, false)?;
                if let Some(underlying) = &enumeration.explicit_underlying_type {
                    self.verify_type(
                        declaration.id,
                        "enum.explicit_underlying_type",
                        underlying,
                        TypePosition::ByValue,
                        aliases,
                        by_value_records,
                    )?;
                }
                let mut children = BTreeSet::new();
                for variant in &enumeration.variants {
                    if !children.insert(variant.id) || !variant.support.is_supported() {
                        return self.unsupported_declaration(
                            declaration.id,
                            "enum variants must be distinct and fully supported",
                        );
                    }
                    if matches!(variant.value, parc::contract::EnumValue::Unevaluated { .. }) {
                        return self.unsupported_declaration(
                            declaration.id,
                            "enum values must be evaluated exactly",
                        );
                    }
                }
            }
            SourceDeclarationKind::TypeAlias(alias) => {
                self.push_alias(declaration.id, declaration.id, aliases)?;
                let result = self.verify_type(
                    declaration.id,
                    "type_alias.target",
                    &alias.target,
                    TypePosition::AliasTarget,
                    aliases,
                    by_value_records,
                );
                aliases.pop();
                result?;
            }
            SourceDeclarationKind::Variable(variable) => {
                if variable.thread_local {
                    return self.unsupported_declaration(
                        declaration.id,
                        "thread-local globals are explicitly rejected",
                    );
                }
                self.verify_type(
                    declaration.id,
                    "variable.type",
                    &variable.ty,
                    TypePosition::ByValue,
                    aliases,
                    by_value_records,
                )?;
            }
            SourceDeclarationKind::Unsupported(_) => {
                return self.unsupported_declaration(
                    declaration.id,
                    "unsupported source declaration entered the strict closure",
                );
            }
        }
        Ok(())
    }

    fn verify_record(
        &self,
        owner: DeclarationId,
        record: &parc::contract::SourceRecord,
        aliases: &mut Vec<DeclarationId>,
        by_value_records: &mut Vec<DeclarationId>,
    ) -> GenerationResult<()> {
        if record.completeness != RecordCompleteness::Complete {
            return self.unsupported_declaration(owner, "by-value record is incomplete or opaque");
        }
        self.require_layout(owner, true)?;
        if record.fields.is_empty() {
            return self.unsupported_declaration(owner, "empty C records are extension-dependent");
        }
        if by_value_records.contains(&owner) {
            return self
                .unsupported_declaration(owner, "by-value record dependency cycle detected");
        }
        by_value_records.push(owner);
        let last = record.fields.len() - 1;
        for (index, field) in record.fields.iter().enumerate() {
            if !field.support.is_supported()
                || field.attributes.iter().any(|attribute| {
                    attribute.disposition == AttributeDisposition::UnsupportedAbiRelevant
                })
            {
                by_value_records.pop();
                return self.unsupported_declaration(owner, "record field is not fully supported");
            }
            if field.bit_width.is_some() {
                by_value_records.pop();
                return self.unsupported_declaration(owner, "bitfields are explicitly rejected");
            }
            let flexible = matches!(
                field.ty.kind,
                CTypeKind::Array {
                    bound: ArrayBound::Flexible,
                    ..
                }
            );
            if flexible && (record.kind != RecordKind::Struct || index != last) {
                by_value_records.pop();
                return self.unsupported_declaration(
                    owner,
                    "a flexible array is legal only as the final struct field",
                );
            }
            self.verify_type(
                owner,
                &format!("record.fields[{index}]"),
                &field.ty,
                TypePosition::ByValue,
                aliases,
                by_value_records,
            )?;
        }
        by_value_records.pop();
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn verify_type(
        &self,
        owner: DeclarationId,
        path: &str,
        ty: &CType,
        position: TypePosition,
        aliases: &mut Vec<DeclarationId>,
        by_value_records: &mut Vec<DeclarationId>,
    ) -> GenerationResult<()> {
        self.verify_type_metadata(owner, path, ty)?;
        match &ty.kind {
            CTypeKind::Void => {
                if !matches!(position, TypePosition::Return | TypePosition::BehindPointer) {
                    return self.unsupported_type(owner, path, "void appears in a value position");
                }
            }
            CTypeKind::Bool | CTypeKind::Integer(_) | CTypeKind::Floating(_) => {}
            CTypeKind::Complex(_) => {
                return self.unsupported_type(
                    owner,
                    path,
                    "complex C types are explicitly rejected",
                );
            }
            CTypeKind::Pointer(pointee) => {
                self.verify_type(
                    owner,
                    &format!("{path}.pointee"),
                    pointee,
                    TypePosition::BehindPointer,
                    aliases,
                    by_value_records,
                )?;
            }
            CTypeKind::Array {
                element,
                bound,
                parameter_qualifiers,
            } => {
                if *parameter_qualifiers != TypeQualifiers::NONE
                    && position != TypePosition::Parameter
                {
                    return self.unsupported_type(
                        owner,
                        path,
                        "parameter-only array qualifiers appear outside a parameter",
                    );
                }
                match (bound, position) {
                    (ArrayBound::Fixed { elements }, _) if *elements != 0 => {}
                    (ArrayBound::Flexible, TypePosition::ByValue) => {}
                    (ArrayBound::Incomplete, TypePosition::Parameter)
                    | (ArrayBound::Flexible, TypePosition::Parameter)
                    | (ArrayBound::StaticMinimum { .. }, TypePosition::Parameter) => {}
                    _ => {
                        return self.unsupported_type(
                            owner,
                            path,
                            "array bound has no certified Rust ABI representation",
                        );
                    }
                }
                let element_position = if position == TypePosition::Parameter {
                    TypePosition::BehindPointer
                } else {
                    TypePosition::ByValue
                };
                self.verify_type(
                    owner,
                    &format!("{path}.element"),
                    element,
                    element_position,
                    aliases,
                    by_value_records,
                )?;
            }
            CTypeKind::Function(function) => {
                if !matches!(
                    position,
                    TypePosition::BehindPointer | TypePosition::Parameter
                ) {
                    return self.unsupported_type(
                        owner,
                        path,
                        "bare function type appears outside pointer/parameter adjustment",
                    );
                }
                lower_calling_convention(
                    owner,
                    &function.calling_convention,
                    self.source.source().target().architecture(),
                    self.source.source().target().operating_system(),
                )?;
                if !matches!(
                    function.prototype,
                    FunctionPrototype::Prototyped { variadic: false }
                ) {
                    return self.unsupported_type(
                        owner,
                        path,
                        "variadic or unspecified callbacks are explicitly rejected",
                    );
                }
                self.verify_type(
                    owner,
                    &format!("{path}.return_type"),
                    &function.return_type,
                    TypePosition::Return,
                    aliases,
                    by_value_records,
                )?;
                for (index, parameter) in function.parameters.iter().enumerate() {
                    self.verify_type(
                        owner,
                        &format!("{path}.parameters[{index}]"),
                        &parameter.ty,
                        TypePosition::Parameter,
                        aliases,
                        by_value_records,
                    )?;
                }
            }
            CTypeKind::AliasRef(target) => {
                let declaration = self.declaration(owner, *target)?;
                let SourceDeclarationKind::TypeAlias(alias) = &declaration.kind else {
                    return self.unsupported_type(
                        owner,
                        path,
                        "AliasRef does not reference a type-alias declaration",
                    );
                };
                self.push_alias(owner, *target, aliases)?;
                let result = self.verify_type(
                    owner,
                    &format!("{path}.alias_target"),
                    &alias.target,
                    position,
                    aliases,
                    by_value_records,
                );
                aliases.pop();
                result?;
            }
            CTypeKind::RecordRef(target) => {
                let declaration = self.declaration(owner, *target)?;
                let SourceDeclarationKind::Record(record) = &declaration.kind else {
                    return self.unsupported_type(
                        owner,
                        path,
                        "RecordRef does not reference a record declaration",
                    );
                };
                // Naming an opaque record is not using one. A use of the
                // alias carries its own position, so `void f(T)` is still
                // refused while `T *` is not.
                if position != TypePosition::BehindPointer && position != TypePosition::AliasTarget
                {
                    if self.requirement(owner, *target)? != ClosureRequirement::Definition {
                        return self.unsupported_type(
                            owner,
                            path,
                            "opaque record is used by value",
                        );
                    }
                    self.verify_record(*target, record, aliases, by_value_records)?;
                }
            }
            CTypeKind::EnumRef(target) => {
                let declaration = self.declaration(owner, *target)?;
                if !matches!(declaration.kind, SourceDeclarationKind::Enum(_)) {
                    return self.unsupported_type(
                        owner,
                        path,
                        "EnumRef does not reference an enum declaration",
                    );
                }
                self.require_layout(*target, false)?;
            }
            CTypeKind::Unsupported { .. } => {
                return self.unsupported_type(
                    owner,
                    path,
                    "unsupported PARC type node entered the strict closure",
                );
            }
        }
        Ok(())
    }

    fn verify_type_metadata(
        &self,
        owner: DeclarationId,
        path: &str,
        ty: &CType,
    ) -> GenerationResult<()> {
        if !ty.support.is_supported() {
            return self.unsupported_type(owner, path, "type support is not fully accepted");
        }
        if ty.qualifiers.is_atomic {
            return self.unsupported_type(owner, path, "_Atomic semantics are not modeled");
        }
        if ty.qualifiers.is_volatile {
            return self.unsupported_type(owner, path, "volatile semantics are not modeled");
        }
        if ty.nullability != parc::contract::Nullability::Unspecified
            && !matches!(ty.kind, CTypeKind::Pointer(_) | CTypeKind::Function(_))
        {
            return self.unsupported_type(owner, path, "nullability appears on a non-pointer type");
        }
        Ok(())
    }

    fn require_layout(&self, declaration: DeclarationId, record: bool) -> GenerationResult<()> {
        let package = self.evidence.package();
        let layout = package
            .layouts()
            .binary_search_by_key(&declaration, LayoutEvidence::declaration)
            .ok()
            .map(|index| &package.layouts()[index])
            .ok_or(GenerationError::MissingLayoutEvidence { declaration })?;
        let matches_kind = matches!(
            (record, layout),
            (true, LayoutEvidence::Record(_)) | (false, LayoutEvidence::Enum(_))
        );
        if !matches_kind
            || layout.source_fingerprint() != self.source.source().fingerprint()
            || layout.target_fingerprint() != self.source.source().target_fingerprint()
        {
            return Err(GenerationError::LayoutMismatch {
                declaration,
                reason: "layout kind or source/target fingerprint is stale",
            });
        }
        Ok(())
    }

    fn declaration(
        &self,
        owner: DeclarationId,
        target: DeclarationId,
    ) -> GenerationResult<&SourceDeclaration> {
        if !self.requirements.contains_key(&target) {
            return self.unsupported_type(
                owner,
                "declaration_graph",
                "named type reference escapes the selected closed world",
            );
        }
        self.source
            .source()
            .declaration(target)
            .ok_or(GenerationError::MissingDeclaration {
                declaration: target,
            })
    }

    fn requirement(
        &self,
        owner: DeclarationId,
        target: DeclarationId,
    ) -> GenerationResult<ClosureRequirement> {
        self.requirements
            .get(&target)
            .copied()
            .ok_or_else(|| GenerationError::UnsupportedType {
                declaration: owner,
                path: "declaration_graph".to_owned(),
                reason: "declaration requirement is absent from the selected closed world",
            })
    }

    fn push_alias(
        &self,
        owner: DeclarationId,
        alias: DeclarationId,
        stack: &mut Vec<DeclarationId>,
    ) -> GenerationResult<()> {
        if stack.contains(&alias) {
            return self.unsupported_type(owner, "alias_graph", "type-alias cycle detected");
        }
        stack.push(alias);
        Ok(())
    }

    fn unsupported_type<T>(
        &self,
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

    fn unsupported_declaration<T>(
        &self,
        declaration: DeclarationId,
        reason: &'static str,
    ) -> GenerationResult<T> {
        Err(GenerationError::UnsupportedDeclaration {
            declaration,
            reason,
        })
    }
}

/// Independent post-lowering verifier. This deliberately walks the immutable
/// projection instead of trusting the lowering implementation that produced
/// it.
pub(crate) fn verify_projection(projection: &ValidatedRustProjection) -> GenerationResult<()> {
    let items: BTreeMap<_, _> = projection
        .items()
        .iter()
        .map(|item| (item.declaration(), item))
        .collect();
    if items.len() != projection.items().len() {
        return invariant("post-lowering projection repeats a declaration");
    }
    for item in projection.items() {
        let mut aliases = Vec::new();
        match item {
            RustItem::Function(function) => {
                if function.variadic() {
                    return invariant("post-lowering projection contains a variadic function");
                }
                verify_rust_type(
                    function.return_type(),
                    TypePosition::Return,
                    &items,
                    &mut aliases,
                )?;
                for parameter in function.parameters() {
                    if matches!(parameter.ty().kind(), RustTypeKind::Void) {
                        return invariant("post-lowering projection contains a void parameter");
                    }
                    verify_rust_type(parameter.ty(), TypePosition::ByValue, &items, &mut aliases)?;
                }
            }
            RustItem::Record(record) => match record.kind() {
                RustRecordKind::Opaque => {
                    if !record.fields().is_empty()
                        || record.size_bits().is_some()
                        || record.alignment_bits().is_some()
                        || record.packing_bits().is_some()
                    {
                        return invariant("opaque record carries concrete layout state");
                    }
                }
                RustRecordKind::Struct | RustRecordKind::Union => {
                    let (Some(size_bits), Some(alignment_bits)) =
                        (record.size_bits(), record.alignment_bits())
                    else {
                        return invariant("concrete record lacks measured layout");
                    };
                    if size_bits == 0
                        || size_bits % 8 != 0
                        || alignment_bits < 8
                        || !alignment_bits.is_power_of_two()
                    {
                        return invariant("concrete record carries an invalid byte layout");
                    }
                    if record.packing_bits().is_some_and(|packing| {
                        packing < 8
                            || !packing.is_power_of_two()
                            || packing % 8 != 0
                            || alignment_bits > packing
                    }) {
                        return invariant("concrete record carries an invalid packing cap");
                    }
                    for (index, field) in record.fields().iter().enumerate() {
                        if field.offset_bits() % 8 != 0 || field.size_bits() % 8 != 0 {
                            return invariant("record field is not byte-addressable");
                        }
                        if record.kind() == RustRecordKind::Union && field.offset_bits() != 0 {
                            return invariant("union field has a nonzero measured offset");
                        }
                        if matches!(field.ty().kind(), RustTypeKind::FlexibleArray { .. })
                            && (record.kind() != RustRecordKind::Struct
                                || index + 1 != record.fields().len())
                        {
                            return invariant("flexible array is not the final struct field");
                        }
                        verify_rust_type(field.ty(), TypePosition::ByValue, &items, &mut aliases)?;
                    }
                }
            },
            RustItem::Enum(enumeration) => {
                if matches!(
                    enumeration.storage(),
                    crate::RustScalar::Bool
                        | crate::RustScalar::CFloat { .. }
                        | crate::RustScalar::CDouble { .. }
                        | crate::RustScalar::F32
                        | crate::RustScalar::F64
                ) {
                    return invariant("enum storage is not an integer scalar");
                }
            }
            RustItem::TypeAlias(alias) => {
                aliases.push(alias.declaration());
                verify_rust_type(
                    alias.target(),
                    TypePosition::AliasTarget,
                    &items,
                    &mut aliases,
                )?;
            }
            RustItem::Variable(variable) => {
                if variable.thread_local() {
                    return invariant("post-lowering projection contains TLS");
                }
                verify_rust_type(variable.ty(), TypePosition::ByValue, &items, &mut aliases)?;
            }
        }
    }
    Ok(())
}

fn verify_rust_type(
    ty: &RustType,
    position: TypePosition,
    items: &BTreeMap<DeclarationId, &RustItem>,
    aliases: &mut Vec<DeclarationId>,
) -> GenerationResult<()> {
    if !matches!(ty.support(), SupportStatus::Supported) {
        return invariant("post-lowering type retains rejected/partial support");
    }
    match ty.kind() {
        RustTypeKind::Void
            if !matches!(position, TypePosition::Return | TypePosition::BehindPointer) =>
        {
            invariant("void remains in a post-lowering value position")
        }
        RustTypeKind::Void | RustTypeKind::Scalar(_) => Ok(()),
        RustTypeKind::Pointer(pointee) => {
            verify_rust_type(pointee, TypePosition::BehindPointer, items, aliases)
        }
        RustTypeKind::FixedArray { element, elements } => {
            if *elements == 0 {
                return invariant("fixed array has zero elements");
            }
            verify_rust_type(element, TypePosition::ByValue, items, aliases)
        }
        RustTypeKind::FlexibleArray { element } => {
            verify_rust_type(element, TypePosition::ByValue, items, aliases)
        }
        RustTypeKind::Named {
            declaration,
            rust_name,
        } => {
            let item = items
                .get(declaration)
                .ok_or(GenerationError::ProjectionInvariant {
                    reason: "post-lowering named type has no declaration",
                })?;
            if item.rust_name() != rust_name {
                return invariant("post-lowering named type carries a stale Rust identifier");
            }
            match item {
                RustItem::Record(record)
                    if record.kind() == RustRecordKind::Opaque
                        && position != TypePosition::BehindPointer
                        && position != TypePosition::AliasTarget =>
                {
                    invariant("opaque record remains in a by-value Rust position")
                }
                RustItem::TypeAlias(alias) => {
                    if aliases.contains(declaration) {
                        return invariant("post-lowering type-alias cycle detected");
                    }
                    aliases.push(*declaration);
                    let result = verify_rust_type(alias.target(), position, items, aliases);
                    aliases.pop();
                    result
                }
                RustItem::Record(_) | RustItem::Enum(_) => Ok(()),
                RustItem::Function(_) | RustItem::Variable(_) => {
                    invariant("named type references a value declaration")
                }
            }
        }
        RustTypeKind::FunctionPointer {
            parameters,
            return_type,
            variadic,
            ..
        } => {
            if *variadic {
                return invariant("post-lowering callback is variadic");
            }
            for parameter in parameters {
                verify_rust_type(parameter, TypePosition::ByValue, items, aliases)?;
            }
            verify_rust_type(return_type, TypePosition::Return, items, aliases)
        }
    }
}

fn invariant<T>(reason: &'static str) -> GenerationResult<T> {
    Err(GenerationError::ProjectionInvariant { reason })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use parc::contract::{
        CType, CTypeKind, ChildId, ChildRole, DeclarationId, DeclarationIdentity, EntityId,
        EntityNamespace, EntityScope, FileId, Linkage, Nullability, RecordCompleteness, RecordKind,
        SourceDeclaration, SourceDeclarationKind, SourceName, SourceOrigin, SourceProvenance,
        SourceRange, SourceTypeAlias, SupportStatus, TypeQualifiers, Visibility,
    };

    use crate::{
        RustField, RustItem, RustName, RustRecord, RustRecordKind, RustScalar, RustType,
        RustTypeAlias, RustTypeKind, SourceDeclarationMetadata, ValidatedRustProjection,
    };

    use super::{verify_projection, verify_rust_type, TypePosition};

    #[test]
    fn post_verifier_rejects_unknown_names_alias_cycles_and_opaque_by_value() {
        let missing = declaration_id("missing");
        let unknown = named_type(missing, "missing");
        let error = verify_rust_type(
            &unknown,
            TypePosition::ByValue,
            &BTreeMap::new(),
            &mut Vec::new(),
        )
        .expect_err("unknown named type must fail closed");
        assert!(error.to_string().contains("no declaration"));

        let opaque_id = declaration_id("opaque");
        let alias_id = declaration_id("opaque_alias");
        let opaque_projection = projection(vec![
            RustItem::Record(RustRecord {
                declaration: opaque_id,
                rust_name: rust_name("opaque"),
                kind: RustRecordKind::Opaque,
                source_kind: RecordKind::Struct,
                source_completeness: RecordCompleteness::Incomplete,
                fields: Vec::new(),
                size_bits: None,
                alignment_bits: None,
                packing_bits: None,
                source: metadata(opaque_id, "opaque"),
            }),
            RustItem::TypeAlias(RustTypeAlias {
                declaration: alias_id,
                rust_name: rust_name("opaque_alias"),
                target: named_type(opaque_id, "opaque"),
                source: metadata(alias_id, "opaque_alias"),
            }),
        ]);
        // `typedef struct T T;` is the opaque-handle idiom every real C library
        // uses. The alias names the record; it does not use one.
        verify_projection(&opaque_projection).expect("naming an opaque record is not using one");

        // What must still fail is a *use* of that alias by value, which the
        // alias walk catches because it recurses at the caller's position.
        let mut aliases = Vec::new();
        let items = opaque_projection
            .items()
            .iter()
            .map(|item| (item.declaration(), item))
            .collect::<BTreeMap<_, _>>();
        let alias_use = named_type(alias_id, "opaque_alias");
        assert!(
            verify_rust_type(&alias_use, TypePosition::ByValue, &items, &mut aliases)
                .expect_err("opaque behind an alias is still opaque by value")
                .to_string()
                .contains("opaque")
        );
        assert!(verify_rust_type(
            &alias_use,
            TypePosition::BehindPointer,
            &items,
            &mut Vec::new()
        )
        .is_ok());

        let first = declaration_id("cycle_a");
        let second = declaration_id("cycle_b");
        let cycle_projection = projection(vec![
            RustItem::TypeAlias(RustTypeAlias {
                declaration: first,
                rust_name: rust_name("cycle_a"),
                target: named_type(second, "cycle_b"),
                source: metadata(first, "cycle_a"),
            }),
            RustItem::TypeAlias(RustTypeAlias {
                declaration: second,
                rust_name: rust_name("cycle_b"),
                target: named_type(first, "cycle_a"),
                source: metadata(second, "cycle_b"),
            }),
        ]);
        assert!(verify_projection(&cycle_projection)
            .expect_err("alias cycle must fail")
            .to_string()
            .contains("cycle"));
    }

    #[test]
    fn post_verifier_rejects_flexible_array_placement_and_nonzero_union_offsets() {
        let owner = declaration_id("bad_flexible");
        let flexible = RustType {
            qualifiers: TypeQualifiers::NONE,
            nullability: Nullability::Unspecified,
            support: SupportStatus::Supported,
            kind: RustTypeKind::FlexibleArray {
                element: Box::new(scalar()),
            },
        };
        let flexible_projection = projection(vec![RustItem::Record(RustRecord {
            declaration: owner,
            rust_name: rust_name("bad_flexible"),
            kind: RustRecordKind::Struct,
            source_kind: RecordKind::Struct,
            source_completeness: RecordCompleteness::Complete,
            fields: vec![
                field(owner, "tail", flexible, 0),
                field(owner, "after", scalar(), 0),
            ],
            size_bits: Some(32),
            alignment_bits: Some(32),
            packing_bits: None,
            source: metadata(owner, "bad_flexible"),
        })]);
        assert!(verify_projection(&flexible_projection)
            .expect_err("non-tail flexible member must fail")
            .to_string()
            .contains("flexible"));

        let owner = declaration_id("bad_union");
        let union_projection = projection(vec![RustItem::Record(RustRecord {
            declaration: owner,
            rust_name: rust_name("bad_union"),
            kind: RustRecordKind::Union,
            source_kind: RecordKind::Union,
            source_completeness: RecordCompleteness::Complete,
            fields: vec![field(owner, "member", scalar(), 32)],
            size_bits: Some(32),
            alignment_bits: Some(32),
            packing_bits: None,
            source: metadata(owner, "bad_union"),
        })]);
        assert!(verify_projection(&union_projection)
            .expect_err("nonzero union offset must fail")
            .to_string()
            .contains("union"));
    }

    fn projection(items: Vec<RustItem>) -> ValidatedRustProjection {
        let declarations: Vec<_> = items.iter().map(RustItem::declaration).collect();
        ValidatedRustProjection::try_new(target_fingerprint(), items, Vec::new(), &declarations)
            .expect("shape-only projection")
    }

    fn field(owner: DeclarationId, name: &str, ty: RustType, offset_bits: u64) -> RustField {
        RustField {
            child: ChildId::named(owner, ChildRole::Field, name).expect("field id"),
            rust_name: rust_name(name),
            source_name: None,
            ty,
            offset_bits,
            size_bits: 32,
            alignment_bits: Some(32),
            range: SourceRange {
                file: FileId::from_logical_path("h4/verify.h").expect("file id"),
                start: 0,
                end: 1,
            },
            provenance: SourceProvenance {
                origin: SourceOrigin::Generated,
                include_chain: Vec::new(),
                macro_expansions: Vec::new(),
            },
            attributes: Vec::new(),
            support: SupportStatus::Supported,
            identity_tokens: vec![name.to_owned()],
            duplicate_ordinal: 0,
        }
    }

    fn scalar() -> RustType {
        RustType {
            qualifiers: TypeQualifiers::NONE,
            nullability: Nullability::Unspecified,
            support: SupportStatus::Supported,
            kind: RustTypeKind::Scalar(RustScalar::CInt {
                storage_bits: 32,
                alignment_bits: 32,
            }),
        }
    }

    fn named_type(declaration: DeclarationId, name: &str) -> RustType {
        RustType {
            qualifiers: TypeQualifiers::NONE,
            nullability: Nullability::Unspecified,
            support: SupportStatus::Supported,
            kind: RustTypeKind::Named {
                declaration,
                rust_name: rust_name(name),
            },
        }
    }

    fn declaration_id(name: &str) -> DeclarationId {
        DeclarationId::from_entity(
            EntityId::named(
                EntityNamespace::Ordinary,
                EntityScope::TranslationUnit,
                name,
            )
            .expect("entity id"),
        )
    }

    fn rust_name(name: &str) -> RustName {
        RustName::checked(name.to_owned()).expect("Rust name")
    }

    fn metadata(id: DeclarationId, name: &str) -> SourceDeclarationMetadata {
        SourceDeclarationMetadata::from_source(&SourceDeclaration {
            id,
            identity: DeclarationIdentity::Named {
                namespace: EntityNamespace::Ordinary,
                scope: EntityScope::TranslationUnit,
                normalized_name: name.to_owned(),
            },
            name: Some(SourceName {
                normalized: name.to_owned(),
                original: name.to_owned(),
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
        })
    }

    fn target_fingerprint() -> parc::contract::TargetFingerprint {
        parc::contract::decode_source_package(parc::contract::corpus::COMPLETE_SOURCE_PACKAGE_JSON)
            .expect("target corpus")
            .target_fingerprint()
    }
}
