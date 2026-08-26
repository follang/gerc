#![cfg(feature = "pipeline-native")]

#[path = "pipeline_support/matrix.rs"]
mod matrix;

use std::{
    collections::BTreeSet,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

use gerc::{
    generate, GenerationBundle, GenerationErrorCode, GenerationRequest, ItemSelection, RustItem,
    RustLinkArtifactKind, RustLinkAtom, RustRecordKind,
};
use linc::{
    contract::{
        AnalysisPolicy, AnalysisRequest, ArtifactFingerprint, NativeInput,
        ProbeEnvironmentIdentity, ProbeEnvironmentPolicy, ProbeExecutionPolicy, ProbePolicy,
        ProbeResourceLimits, ResolutionPolicy, RunnerPolicy, ValidatedLinkAnalysis,
    },
    native::{
        CertificationToolchain, LibraryPreference, NativeAnalyzer, NativeError, NativeInspector,
        NativeResolver, ResolverConfiguration,
    },
};
use matrix::CertificationState;
use parc::{
    contract::{
        Architecture, CDataModel, CDataModelClass, CharSignedness, CompilerFamily,
        CompleteSourcePackage, Completeness, CompletionBlocker, DeclarationId, Endian, Environment,
        ExtensionFamily, ExtensionProfile, FloatingFormat, FloatingLayout, IntegerLayout,
        LanguageStandard, MacroForm, NormalizedCompilerArg, ObjectFormat, OperatingSystem,
        ScalarLayout, Selection, SignedIntegerRepresentation, Signedness, SourceDeclarationKind,
        SourcePackage, TargetSpec, TargetSpecParts, Vendor,
    },
    scan::{scan_headers, PathMapping, PathMappingRule, PreprocessorMode, ScanConfig},
};

static NEXT_SCRATCH: AtomicU64 = AtomicU64::new(0);

#[test]
fn h5_matrices_are_exact_three_state_and_inventory_closed() {
    for rows in [
        matrix::TYPE_MATRIX,
        matrix::PLATFORM_MATRIX,
        matrix::PROVIDER_FAILURES,
    ] {
        let states = rows.iter().map(|row| row.state).collect::<BTreeSet<_>>();
        assert_eq!(
            states,
            BTreeSet::from([
                CertificationState::SupportedAndTested,
                CertificationState::ExplicitlyRejected,
                CertificationState::ExperimentalNotForFol,
            ])
            .intersection(&states)
            .copied()
            .collect(),
            "matrix contains an unknown certification state"
        );
        let mut constructs = BTreeSet::new();
        for row in rows {
            assert!(constructs.insert(row.construct), "duplicate matrix row");
            assert!(!row.owner.is_empty());
            assert!(!row.case.is_empty());
            assert_eq!(
                row.state.label(),
                match row.state {
                    CertificationState::SupportedAndTested => "supported-and-tested",
                    CertificationState::ExplicitlyRejected => "explicitly-rejected",
                    CertificationState::ExperimentalNotForFol => "experimental-not-for-FOL",
                }
            );
            if row.state != CertificationState::SupportedAndTested {
                assert!(
                    row.stable_code.is_some(),
                    "rejection/note must be classified"
                );
            }
        }
    }

    let type_states = matrix::TYPE_MATRIX
        .iter()
        .map(|row| row.state)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        type_states,
        BTreeSet::from([
            CertificationState::SupportedAndTested,
            CertificationState::ExplicitlyRejected,
            CertificationState::ExperimentalNotForFol,
        ])
    );
    let required = matrix::REQUIRED_RUNTIME_CASES
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    for row in matrix::TYPE_MATRIX.iter().chain(matrix::PROVIDER_FAILURES) {
        assert!(
            required.contains(row.case),
            "untracked matrix case: {row:?}"
        );
    }
}

#[test]
fn h5_production_pipeline_certifies_positive_and_owning_layer_negative_cases() {
    if std::env::var_os("GERC_H5_RUN").is_none() {
        return;
    }

    let harness = Harness::build();
    let mut executed = BTreeSet::new();

    let positive = certify_positive_pipeline(&harness);
    executed.insert("positive-abi-roundtrip");
    certify_macro_policy(&positive.bundle);
    executed.insert("preserve-nonemitted-macros");

    certify_gerc_rejections(&harness, &mut executed);
    certify_parc_rejections(&harness, &mut executed);
    certify_linc_rejections(&harness, &mut executed);
    certify_provider_failures(&harness, &mut executed);
    certify_stale_evidence_rejection(&harness, &positive.evidence);
    executed.insert("reject-stale-evidence");
    certify_platform_boundary(&harness);
    executed.insert("reject-uncertified-platforms");

    assert_eq!(
        executed,
        matrix::REQUIRED_RUNTIME_CASES
            .iter()
            .copied()
            .collect::<BTreeSet<_>>()
    );
}

struct Harness {
    scratch: Scratch,
    fixture: PathBuf,
    compiler: PathBuf,
    rustc: PathBuf,
    toolchain: CertificationToolchain,
    target: TargetSpec,
    source: SourcePackage,
    artifacts: Artifacts,
}

impl Harness {
    fn build() -> Self {
        let compiler = explicit_tool("GERC_H5_GCC", "gcc");
        Self::build_with_compiler("gerc-h5-pipeline-gcc", compiler, CompilerFamily::Gcc)
    }

    fn build_with_compiler(
        scratch_prefix: &str,
        compiler: PathBuf,
        expected_family: CompilerFamily,
    ) -> Self {
        let scratch = Scratch::new(scratch_prefix);
        let fixture =
            fs::canonicalize(Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/pipeline-fixtures"))
                .expect("canonical H5 fixture directory");
        let ar = explicit_tool("GERC_H5_AR", "ar");
        let rustc = explicit_tool("RUSTC", "rustc");
        let toolchain =
            CertificationToolchain::observe(compiler.clone(), Vec::new(), probe_limits())
                .expect("bounded H5 toolchain observation");
        let target = target_for_toolchain(&toolchain, expected_family);
        assert_eq!(target.triple(), "x86_64-unknown-linux-gnu");
        assert_eq!(target.object_format(), ObjectFormat::Elf);
        assert_eq!(target.compiler().family(), expected_family);
        let source = scan_builtin(&target, &fixture, None);
        assert_eq!(source.completeness(), &Completeness::Complete);
        let artifacts = build_artifacts(scratch.path(), &fixture, &compiler, &ar);
        Self {
            scratch,
            fixture,
            compiler,
            rustc,
            toolchain,
            target,
            source,
            artifacts,
        }
    }

    fn full_inputs(&self) -> Vec<NativeInput> {
        vec![
            NativeInput::StaticLibraryPath(self.artifacts.provider.clone()),
            NativeInput::StaticLibraryPath(self.artifacts.dependency.clone()),
            NativeInput::ObjectPath(self.artifacts.exact.clone()),
            NativeInput::DynamicLibraryPath(self.artifacts.shared.clone()),
        ]
    }
}

struct Artifacts {
    provider: PathBuf,
    dependency: PathBuf,
    exact: PathBuf,
    shared: PathBuf,
    negative: PathBuf,
    duplicate: PathBuf,
    ambiguous_one: PathBuf,
    ambiguous_two: PathBuf,
    wrong_target: PathBuf,
}

struct PositiveCertification {
    evidence: ValidatedLinkAnalysis,
    bundle: GenerationBundle,
}

fn certify_positive_pipeline(harness: &Harness) -> PositiveCertification {
    let root = declaration_id(&harness.source, "h5_roundtrip", Kind::Function);
    let complete = complete(&harness.source, [root]);
    let inputs = harness.full_inputs();
    let evidence =
        certify(harness, &complete, &inputs).expect("positive LINC production certification");
    let selection = ItemSelection::try_new([root]).expect("positive generation selection");
    let bundle = generate(
        GenerationRequest::try_new(&complete, &evidence, &selection)
            .expect("positive typed generation request"),
    )
    .expect("positive strict generation");

    assert_eq!(
        evidence.package().source_fingerprint(),
        complete.source().fingerprint()
    );
    assert_eq!(
        evidence.package().target_fingerprint(),
        complete.source().target_fingerprint()
    );
    assert_eq!(
        bundle.manifest().source_fingerprint(),
        complete.source().fingerprint()
    );
    assert_eq!(
        bundle.manifest().target_fingerprint(),
        complete.source().target_fingerprint()
    );
    assert_eq!(
        bundle.manifest().evidence_fingerprint(),
        evidence.package().fingerprint()
    );
    assert_ne!(
        bundle.manifest().generation_fingerprint().as_bytes(),
        &[0; 32]
    );

    let expected_paths = [
        &harness.artifacts.provider,
        &harness.artifacts.dependency,
        &harness.artifacts.exact,
        &harness.artifacts.shared,
    ];
    assert_eq!(bundle.link_plan().atoms().len(), expected_paths.len());
    for (index, (atom, expected_path)) in bundle
        .link_plan()
        .atoms()
        .iter()
        .zip(expected_paths)
        .enumerate()
    {
        let RustLinkAtom::Artifact(artifact) = atom else {
            panic!("H5 link atom {index} is not an exact artifact: {atom:?}");
        };
        assert_eq!(artifact.canonical_path(), expected_path);
        assert_eq!(
            artifact.artifact_fingerprint(),
            ArtifactFingerprint::from_content(&fs::read(expected_path).expect("artifact bytes"))
        );
    }
    assert_eq!(
        bundle.link_plan().atoms()[0],
        RustLinkAtom::Artifact(match &bundle.link_plan().atoms()[0] {
            RustLinkAtom::Artifact(artifact) => artifact.clone(),
            _ => unreachable!(),
        })
    );
    assert!(matches!(
        &bundle.link_plan().atoms()[0],
        RustLinkAtom::Artifact(artifact) if artifact.kind() == RustLinkArtifactKind::StaticLibrary
    ));
    assert!(matches!(
        &bundle.link_plan().atoms()[2],
        RustLinkAtom::Artifact(artifact) if artifact.kind() == RustLinkArtifactKind::Object
    ));
    assert!(matches!(
        &bundle.link_plan().atoms()[3],
        RustLinkAtom::Artifact(artifact) if artifact.kind() == RustLinkArtifactKind::DynamicLibrary
    ));

    compile_and_run_generated(harness, &bundle, root);
    PositiveCertification { evidence, bundle }
}

fn certify_macro_policy(bundle: &GenerationBundle) {
    let integer = bundle
        .projection()
        .macros()
        .iter()
        .find(|value| value.source_name() == "H5_INTEGER_MACRO")
        .expect("integer macro");
    assert!(integer.emitted());
    let nonemitted = bundle
        .projection()
        .macros()
        .iter()
        .filter(|value| matches!(value.source_name(), "H5_STRING_MACRO" | "H5_FUNCTION_MACRO"))
        .collect::<Vec<_>>();
    assert_eq!(nonemitted.len(), 2);
    assert!(nonemitted.iter().all(|value| !value.emitted()));
    assert!(nonemitted
        .iter()
        .any(|value| value.form() == MacroForm::FunctionLike));
    for source_macro in nonemitted {
        assert!(bundle.diagnostics().iter().any(|diagnostic| {
            diagnostic.stable_code() == "GERC-N3000"
                && diagnostic.macro_id() == Some(source_macro.macro_id())
        }));
    }
}

fn certify_gerc_rejections(harness: &Harness, executed: &mut BTreeSet<&'static str>) {
    let cases = [
        ("h5_bits", Kind::Record, "reject-bitfields", "GERC-E2002"),
        ("h5_tls", Kind::Variable, "reject-tls", "GERC-E2002"),
    ];
    for (name, kind, case, expected) in cases {
        let root = declaration_id(&harness.source, name, kind);
        let mut roots = vec![root];
        if matches!(kind, Kind::Variable) {
            roots.push(declaration_id(
                &harness.source,
                "h5_roundtrip",
                Kind::Function,
            ));
        }
        let complete = complete(&harness.source, roots);
        let evidence = certify(harness, &complete, &harness.full_inputs())
            .expect("LINC production certifier accepts the GERC-owned case");
        let selection = ItemSelection::try_new([root]).expect("rejection selection");
        let error = generate(
            GenerationRequest::try_new(&complete, &evidence, &selection)
                .expect("typed GERC rejection request"),
        )
        .expect_err("construct must fail closed in GERC");
        assert_eq!(error.stable_code(), expected, "case {case}: {error}");
        executed.insert(case);
    }
}

fn certify_parc_rejections(harness: &Harness, executed: &mut BTreeSet<&'static str>) {
    let external = scan_external(&harness.target, &harness.fixture, &harness.compiler);
    assert!(matches!(
        external.completeness(),
        Completeness::Partial { .. }
    ));
    assert!(external
        .diagnostics()
        .iter()
        .any(|diagnostic| diagnostic.code.as_str() == "PARC-P0001"));
    let root = declaration_id(&external, "h5_roundtrip", Kind::Function);
    let error = external
        .into_complete(&Selection::only([root]).expect("external root"))
        .expect_err("external preprocessing is provenance-partial");
    assert!(error.blockers().iter().any(|blocker| {
        matches!(blocker, CompletionBlocker::PackageIncomplete { reasons }
            if reasons.iter().any(|reason| reason.code.as_str() == "PARC-P0001"))
    }));
    executed.insert("reject-partial-source");

    let opaque = declaration_id(&harness.source, "h5_opaque_value", Kind::Function);
    let error = harness
        .source
        .clone()
        .into_complete(&Selection::only([opaque]).expect("opaque root"))
        .expect_err("opaque by value must not produce a CompleteSourcePackage");
    assert!(error
        .blockers()
        .iter()
        .any(|blocker| matches!(blocker, CompletionBlocker::IncompleteRecord { .. })));
    executed.insert("reject-opaque-by-value");

    let vector_source = scan_builtin(
        &harness.target,
        &harness.fixture,
        Some(("GERC_H5_ENABLE_VECTOR", "1")),
    );
    let vector = declaration_id(&vector_source, "h5_vector_value", Kind::Function);
    let error = vector_source
        .into_complete(&Selection::only([vector]).expect("vector root"))
        .expect_err("vector closure must remain unsupported");
    assert!(error
        .blockers()
        .iter()
        .any(|blocker| matches!(blocker, CompletionBlocker::Unsupported { .. })));
    executed.insert("reject-vector-closure");

    let cpp = scan_cpp(&harness.target, &harness.fixture);
    assert!(matches!(
        cpp.completeness(),
        Completeness::Partial { .. } | Completeness::Rejected { .. }
    ));
    assert!(cpp
        .diagnostics()
        .iter()
        .any(|diagnostic| diagnostic.code.as_str() == "PARC-P0002"));
    executed.insert("reject-cpp-source");

    {
        let define = "GERC_H5_ENABLE_BIT_INT";
        let name = "h5_bit_int";
        let case = "reject-bit-int";
        let code = "PARC-P1107";
        let unsupported = scan_builtin(&harness.target, &harness.fixture, Some((define, "1")));
        assert!(
            matches!(unsupported.completeness(), Completeness::Partial { .. }),
            "{define} must remain provenance-partial: {:?}",
            unsupported.completeness()
        );
        assert!(unsupported
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code.as_str() == code));
        let root = declaration_id(&unsupported, name, Kind::Function);
        let error = unsupported
            .into_complete(&Selection::only([root]).expect("unsupported PARC root"))
            .expect_err("unsupported source must not cross the PARC completeness boundary");
        // The refusal names the declaration rather than the package: the
        // selected root is what `_BitInt(17)` made unsupported.
        assert!(error.blockers().iter().any(|blocker| {
            matches!(blocker, CompletionBlocker::Unsupported { id, .. } if *id == root)
        }));
        executed.insert(case);
    }
}

fn certify_linc_rejections(harness: &Harness, executed: &mut BTreeSet<&'static str>) {
    let cases = [
        ("h5_long_double", "reject-long-double", "LINC-E3014", None),
        ("h5_int128", "reject-int128", "LINC-E3014", None),
        ("h5_complex", "reject-complex", "LINC-E3014", None),
        ("h5_variadic", "reject-variadic", "LINC-E3050", None),
        (
            "h5_msabi",
            "reject-ms-abi-on-linux",
            "LINC-E3050",
            Some("GERC_H5_ENABLE_MS_ABI"),
        ),
    ];
    for (name, case, expected, define) in cases {
        let source = define.map_or_else(
            || harness.source.clone(),
            |define| scan_builtin(&harness.target, &harness.fixture, Some((define, "1"))),
        );
        assert_eq!(source.completeness(), &Completeness::Complete);
        let root = declaration_id(&source, name, Kind::Function);
        let complete = complete(&source, [root]);
        let error = certify(harness, &complete, &harness.full_inputs())
            .expect_err("construct must fail closed in the LINC production certifier");
        assert_eq!(error.code(), expected, "case {case}: {error}");
        executed.insert(case);
    }
}

fn certify_provider_failures(harness: &Harness, executed: &mut BTreeSet<&'static str>) {
    let cases = [
        (
            "h5_missing",
            "reject-missing",
            vec![NativeInput::StaticLibraryPath(
                harness.artifacts.negative.clone(),
            )],
            "LINC-E3040",
        ),
        (
            "h5_hidden",
            "reject-hidden",
            vec![NativeInput::StaticLibraryPath(
                harness.artifacts.negative.clone(),
            )],
            "LINC-E3040",
        ),
        (
            "h5_weak",
            "reject-weak",
            vec![NativeInput::StaticLibraryPath(
                harness.artifacts.negative.clone(),
            )],
            "LINC-E3040",
        ),
        (
            "h5_duplicate",
            "reject-duplicate",
            vec![NativeInput::StaticLibraryPath(
                harness.artifacts.duplicate.clone(),
            )],
            "LINC-E3040",
        ),
        (
            "h5_ambiguous",
            "reject-ambiguous",
            vec![
                NativeInput::StaticLibraryPath(harness.artifacts.ambiguous_one.clone()),
                NativeInput::StaticLibraryPath(harness.artifacts.ambiguous_two.clone()),
            ],
            "LINC-E3040",
        ),
        (
            "h5_wrong_target",
            "reject-wrong-target",
            vec![NativeInput::ObjectPath(
                harness.artifacts.wrong_target.clone(),
            )],
            "LINC-E3007",
        ),
    ];

    for (name, case, inputs, expected) in cases {
        let root = declaration_id(&harness.source, name, Kind::Function);
        let complete = complete(&harness.source, [root]);
        let error = certify(harness, &complete, &inputs)
            .expect_err("provider case must fail closed in LINC");
        assert_eq!(error.code(), expected, "case {case}: {error}");
        executed.insert(case);
    }
}

fn certify_stale_evidence_rejection(harness: &Harness, evidence: &ValidatedLinkAnalysis) {
    let stale = scan_builtin(&harness.target, &harness.fixture, Some(("H5_STALE", "1")));
    assert_ne!(stale.fingerprint(), harness.source.fingerprint());
    assert_eq!(
        stale.target_fingerprint(),
        harness.source.target_fingerprint()
    );
    let root = declaration_id(&stale, "h5_roundtrip", Kind::Function);
    let stale = complete(&stale, [root]);
    let selection = ItemSelection::try_new([root]).expect("stale selection");
    let error = GenerationRequest::try_new(&stale, evidence, &selection)
        .expect_err("source-bound evidence cannot be reused after input drift");
    assert_eq!(error.code(), GenerationErrorCode::SourceFingerprintMismatch);
    assert_eq!(error.stable_code(), "GERC-E1100");
}

fn certify_platform_boundary(harness: &Harness) {
    assert_eq!(harness.target.triple(), "x86_64-unknown-linux-gnu");
    assert_eq!(harness.target.object_format(), ObjectFormat::Elf);
    assert_eq!(harness.target.compiler().family(), CompilerFamily::Gcc);
    for row in matrix::PLATFORM_MATRIX
        .iter()
        .filter(|row| row.state == CertificationState::ExplicitlyRejected)
    {
        assert_eq!(row.owner, "H5 gate");
        assert_eq!(row.stable_code, Some("not certified"));
    }

    let Some(clang) = std::env::var_os("GERC_H5_CLANG").filter(|value| !value.is_empty()) else {
        return;
    };
    let clang = canonical(Path::new(&clang));
    let clang_harness =
        Harness::build_with_compiler("gerc-h5-pipeline-clang", clang, CompilerFamily::Clang);
    let clang_positive = certify_positive_pipeline(&clang_harness);
    certify_macro_policy(&clang_positive.bundle);

    assert_eq!(clang_harness.target.triple(), harness.target.triple());
    assert_eq!(clang_harness.target.object_format(), ObjectFormat::Elf);
    assert_ne!(
        clang_harness.target.fingerprint(),
        harness.target.fingerprint()
    );
    assert_ne!(
        clang_harness.source.fingerprint(),
        harness.source.fingerprint()
    );
    assert_ne!(
        clang_positive.evidence.package().target_fingerprint(),
        harness.source.target_fingerprint()
    );
}

fn certify(
    harness: &Harness,
    complete: &CompleteSourcePackage,
    inputs: &[NativeInput],
) -> Result<ValidatedLinkAnalysis, NativeError> {
    let policy = AnalysisPolicy::strict(
        ResolutionPolicy::ExactPathsOnly,
        ProbePolicy::CompileOnly,
        RunnerPolicy::Unavailable,
        ProbeExecutionPolicy::try_new(
            harness.scratch.path().to_owned(),
            ProbeEnvironmentIdentity::try_new(ProbeEnvironmentPolicy::Empty, Vec::new())
                .expect("empty H5 probe environment"),
            probe_limits(),
        )
        .expect("bounded H5 probe execution policy"),
    )
    .expect("strict H5 policy");
    let request = AnalysisRequest::try_new(complete, inputs, policy).expect("H5 analysis request");
    let resolver = NativeResolver::new(
        NativeInspector::default(),
        ResolverConfiguration::new(Vec::new(), LibraryPreference::DynamicOnly, 128)
            .expect("resolver configuration"),
    )
    .expect("native resolver");
    NativeAnalyzer::new(resolver).certify(&request, &harness.toolchain)
}

fn compile_and_run_generated(harness: &Harness, bundle: &GenerationBundle, root: DeclarationId) {
    let generated = bundle
        .files()
        .get("src/lib.rs")
        .and_then(|file| file.utf8_contents())
        .expect("generated H5 Rust source");
    assert!(generated.contains("#![no_std]"));
    assert!(generated.contains("r#type"));
    assert!(generated.contains("r#match"));
    syn::parse_file(generated).expect("generated source parses in the production parser");

    let directory = harness.scratch.path().join("generated-consumer");
    fs::create_dir(&directory).expect("create generated consumer directory");
    let bindings_source = directory.join("bindings.rs");
    let bindings_rlib = directory.join("libh5_bindings.rlib");
    fs::write(&bindings_source, generated).expect("write generated bindings");
    checked(
        Command::new(&harness.rustc)
            .arg("--crate-name=h5_bindings")
            .arg("--crate-type=rlib")
            .arg("--edition=2021")
            .arg("-o")
            .arg(&bindings_rlib)
            .arg(&bindings_source),
        "build generated H5 no_std crate",
    );

    let function = bundle
        .projection()
        .items()
        .iter()
        .find_map(|item| match item {
            RustItem::Function(function) if function.declaration() == root => Some(function),
            _ => None,
        })
        .expect("projected roundtrip function");
    let payload = bundle
        .projection()
        .items()
        .iter()
        .find_map(|item| match item {
            RustItem::Record(record)
                if record.kind() == RustRecordKind::Struct
                    && record
                        .source()
                        .name()
                        .is_some_and(|name| name.normalized == "h5_payload") =>
            {
                Some(record)
            }
            _ => None,
        })
        .expect("projected payload");
    let choice = bundle
        .projection()
        .items()
        .iter()
        .find_map(|item| match item {
            RustItem::Record(record)
                if record.kind() == RustRecordKind::Union
                    && record
                        .source()
                        .name()
                        .is_some_and(|name| name.normalized == "h5_choice") =>
            {
                Some(record)
            }
            _ => None,
        })
        .expect("projected union");
    let field = |name: &str| {
        payload
            .fields()
            .iter()
            .find(|field| {
                field
                    .source_name()
                    .is_some_and(|source| source.normalized == name)
            })
            .unwrap_or_else(|| panic!("projected payload field {name}"))
            .rust_name()
            .as_str()
            .to_owned()
    };
    let choice_integer = choice
        .fields()
        .iter()
        .find(|field| {
            field
                .source_name()
                .is_some_and(|source| source.normalized == "integer")
        })
        .expect("union integer field")
        .rust_name()
        .as_str();
    let source = format!(
        r#"
extern crate h5_bindings as bindings;

unsafe extern "C" fn callback(value: *mut core::ffi::c_int, delta: core::ffi::c_int) {{
    unsafe {{ *value += delta + 1; }}
}}

fn main() {{
    let input = bindings::{payload} {{
        {boolean}: true,
        {plain}: 10,
        {signed_char}: -5,
        {unsigned_char}: 250,
        {signed_short}: -100,
        {unsigned_short}: 100,
        {signed_int}: 20,
        {unsigned_int}: 30,
        {signed_long}: -40,
        {unsigned_long}: 40,
        {signed_long_long}: -50,
        {unsigned_long_long}: 50,
        {single}: 1.5,
        {double}: 2.5,
        {fixed}: [1, 2, 3],
        {nullable}: core::ptr::null_mut(),
        {opaque}: core::ptr::null_mut(),
        {mode}: -3,
        {choice_field}: bindings::{choice} {{
            {choice_integer}: core::mem::ManuallyDrop::new(31),
        }},
        {callback_field}: Some(callback),
        {match_field}: 3,
        {crate_field}: 0x1234,
    }};
    let output = unsafe {{ bindings::{function}(input) }};
    assert!(!output.{boolean});
    assert_eq!(output.{plain}, 11);
    assert_eq!(output.{signed_char}, -7);
    assert_eq!(output.{unsigned_char}, 253);
    assert_eq!(output.{signed_short}, -104);
    assert_eq!(output.{unsigned_short}, 105);
    assert_eq!(output.{signed_int}, 42);
    assert_eq!(output.{unsigned_int}, 37);
    assert_eq!(output.{signed_long}, -48);
    assert_eq!(output.{unsigned_long}, 49);
    assert_eq!(output.{signed_long_long}, -60);
    assert_eq!(output.{unsigned_long_long}, 61);
    assert_eq!(output.{single}, 2.0);
    assert_eq!(output.{double}, 3.75);
    assert_eq!(output.{fixed}, [13, 15, 17]);
    assert!(output.{nullable}.is_null());
    assert!(output.{opaque}.is_null());
    assert_eq!(output.{mode}, 7);
    assert_eq!(unsafe {{ *output.{choice_field}.{choice_integer} }}, 47);
    assert_eq!(output.{match_field}, 20);
    assert_eq!(output.{crate_field}, 0x479e);
}}
"#,
        payload = payload.rust_name().as_str(),
        choice = choice.rust_name().as_str(),
        function = function.rust_name().as_str(),
        boolean = field("boolean"),
        plain = field("plain_character"),
        signed_char = field("signed_character"),
        unsigned_char = field("unsigned_character"),
        signed_short = field("signed_short"),
        unsigned_short = field("unsigned_short"),
        signed_int = field("signed_int"),
        unsigned_int = field("unsigned_int"),
        signed_long = field("signed_long"),
        unsigned_long = field("unsigned_long"),
        signed_long_long = field("signed_long_long"),
        unsigned_long_long = field("unsigned_long_long"),
        single = field("single_precision"),
        double = field("double_precision"),
        fixed = field("fixed_values"),
        nullable = field("nullable"),
        opaque = field("opaque"),
        mode = field("mode"),
        choice_field = field("choice"),
        callback_field = field("callback"),
        match_field = field("match"),
        crate_field = field("crate"),
    );
    let consumer_source = directory.join("consumer.rs");
    fs::write(&consumer_source, source).expect("write generated consumer");
    let executable = directory.join("consumer");
    let mut command = Command::new(&harness.rustc);
    command
        .arg("--crate-name=h5_pipeline_consumer")
        .arg("--edition=2021")
        .arg("--extern")
        .arg(format!("h5_bindings={}", bindings_rlib.display()));
    command.args(
        bundle
            .link_plan()
            .rustc_arguments()
            .expect("typed H5 rustc link arguments")
            .into_arguments(),
    );
    command.arg("-o").arg(&executable).arg(&consumer_source);
    checked(
        &mut command,
        "link generated Rust consumer through typed argv",
    );
    checked(
        Command::new(&executable).env("LD_LIBRARY_PATH", harness.scratch.path()),
        "run H5 C/Rust ABI consumer",
    );
}

fn build_artifacts(root: &Path, fixture: &Path, gcc: &Path, ar: &Path) -> Artifacts {
    let object = |name: &str, source: &str, extra: &[&str]| {
        let output = root.join(name);
        compile_object(gcc, fixture, source, &output, extra);
        output
    };
    let provider_object = object(
        "h5_provider.o",
        "h5_provider.c",
        &["-fPIC", "-DGERC_H5_ENABLE_MS_ABI"],
    );
    let dependency_object = object("h5_dependency.o", "h5_dependency.c", &[]);
    let exact = object("h5_exact.o", "h5_exact.c", &[]);
    let negative_object = object("h5_negative.o", "h5_negative.c", &[]);
    let duplicate_one = object("h5_duplicate_one.o", "h5_duplicate_one.c", &[]);
    let duplicate_two = object("h5_duplicate_two.o", "h5_duplicate_two.c", &[]);
    let ambiguous_one_object = object("h5_ambiguous_one.o", "h5_ambiguous_one.c", &[]);
    let ambiguous_two_object = object("h5_ambiguous_two.o", "h5_ambiguous_two.c", &[]);
    let wrong_target = object("h5_wrong_target.o", "h5_wrong_target.c", &["-m32"]);

    let provider = root.join("libh5_provider.a");
    archive(ar, &provider, &[&provider_object]);
    let dependency = root.join("libh5_dependency.a");
    archive(ar, &dependency, &[&dependency_object]);
    let negative = root.join("libh5_negative.a");
    archive(ar, &negative, &[&negative_object]);
    let duplicate = root.join("libh5_duplicate.a");
    archive(ar, &duplicate, &[&duplicate_one, &duplicate_two]);
    let ambiguous_one = root.join("libh5_ambiguous_one.a");
    archive(ar, &ambiguous_one, &[&ambiguous_one_object]);
    let ambiguous_two = root.join("libh5_ambiguous_two.a");
    archive(ar, &ambiguous_two, &[&ambiguous_two_object]);

    let shared = root.join("libh5_shared.so");
    checked(
        Command::new(gcc)
            .arg("-std=gnu17")
            .arg("-m64")
            .arg("-Wall")
            .arg("-Wextra")
            .arg("-Werror")
            .arg("-fPIC")
            .arg("-nostdlib")
            .arg("-shared")
            .arg(fixture.join("h5_shared.c"))
            .arg("-o")
            .arg(&shared),
        "compile H5 shared provider",
    );
    for path in [
        &provider,
        &dependency,
        &exact,
        &shared,
        &negative,
        &duplicate,
        &ambiguous_one,
        &ambiguous_two,
        &wrong_target,
    ] {
        assert!(path.is_file(), "missing H5 artifact {}", path.display());
    }
    Artifacts {
        provider: canonical(&provider),
        dependency: canonical(&dependency),
        exact: canonical(&exact),
        shared: canonical(&shared),
        negative: canonical(&negative),
        duplicate: canonical(&duplicate),
        ambiguous_one: canonical(&ambiguous_one),
        ambiguous_two: canonical(&ambiguous_two),
        wrong_target: canonical(&wrong_target),
    }
}

fn compile_object(gcc: &Path, fixture: &Path, source: &str, output: &Path, extra: &[&str]) {
    let mut command = Command::new(gcc);
    command
        .arg("-std=gnu17")
        .arg("-m64")
        .arg("-Wall")
        .arg("-Wextra")
        .arg("-Werror")
        .arg("-I")
        .arg(fixture)
        .args(extra)
        .arg("-c")
        .arg(fixture.join(source))
        .arg("-o")
        .arg(output);
    checked(&mut command, &format!("compile H5 object {source}"));
}

fn archive(ar: &Path, output: &Path, objects: &[&Path]) {
    let mut command = Command::new(ar);
    command.arg("crs").arg(output).args(objects);
    checked(&mut command, &format!("archive {}", output.display()));
}

fn scan_builtin(
    target: &TargetSpec,
    fixture: &Path,
    define: Option<(&str, &str)>,
) -> SourcePackage {
    let mut config = scan_config(target, fixture, PreprocessorMode::Builtin);
    if let Some((name, value)) = define {
        config = config.define(name, Some(value.to_owned()));
    }
    scan_headers(&config)
        .expect("builtin H5 scan")
        .into_package()
}

fn scan_external(target: &TargetSpec, fixture: &Path, gcc: &Path) -> SourcePackage {
    scan_headers(&scan_config(
        target,
        fixture,
        PreprocessorMode::External {
            executable: gcc.to_owned(),
        },
    ))
    .expect("external H5 scan")
    .into_package()
}

fn scan_cpp(target: &TargetSpec, fixture: &Path) -> SourcePackage {
    let mapping = PathMapping::try_new([
        PathMappingRule::try_new(fixture, "h5").expect("H5 C++ path mapping rule")
    ])
    .expect("H5 C++ path mapping");
    let config = ScanConfig::new(target.clone(), mapping, PreprocessorMode::Builtin)
        .expect("H5 C++ scan config")
        .entry_header(fixture.join("h5_cpp.hpp"));
    scan_headers(&config)
        .expect("H5 C++ scan report")
        .into_package()
}

fn scan_config(target: &TargetSpec, fixture: &Path, mode: PreprocessorMode) -> ScanConfig {
    let mapping = PathMapping::try_new([
        PathMappingRule::try_new(fixture, "h5").expect("H5 path mapping rule")
    ])
    .expect("H5 path mapping");
    ScanConfig::new(target.clone(), mapping, mode)
        .expect("H5 scan config")
        .entry_header(fixture.join("h5_api.h"))
}

fn target_for_toolchain(
    toolchain: &CertificationToolchain,
    expected_family: CompilerFamily,
) -> TargetSpec {
    assert_eq!(toolchain.compiler_identity().family(), expected_family);
    assert!(
        matches!(
            toolchain.reported_target(),
            "x86_64-unknown-linux-gnu" | "x86_64-linux-gnu" | "x86_64-pc-linux-gnu"
        ),
        "compiler-reported target is outside the explicit H5 GNU alias set: {}",
        toolchain.reported_target()
    );
    assert!(
        toolchain.compiler_sysroot().is_none(),
        "H5 requires the compiler's default empty sysroot identity"
    );
    TargetSpec::try_new(TargetSpecParts {
        triple: "x86_64-unknown-linux-gnu".to_owned(),
        architecture: Architecture::X86_64,
        vendor: Vendor::try_new("unknown").expect("vendor"),
        operating_system: OperatingSystem::Linux,
        environment: Environment::Gnu,
        object_format: ObjectFormat::Elf,
        endian: Endian::Little,
        pointer_width: 64,
        c_data_model: CDataModel {
            class: CDataModelClass::LP64,
            char_bit: 8,
            char_signedness: CharSignedness::Signed,
            signed_integer_representation: SignedIntegerRepresentation::TwosComplement,
            bool_layout: scalar(8, 8),
            char_layout: scalar(8, 8),
            short_layout: scalar(16, 16),
            int_layout: scalar(32, 32),
            long_layout: scalar(64, 64),
            long_long_layout: scalar(64, 64),
            int128_layout: Some(scalar(128, 128)),
            pointer_layout: scalar(64, 64),
            float_layout: FloatingLayout {
                scalar: scalar(32, 32),
                format: FloatingFormat::IeeeBinary32,
            },
            double_layout: FloatingLayout {
                scalar: scalar(64, 64),
                format: FloatingFormat::IeeeBinary64,
            },
            long_double_layout: FloatingLayout {
                scalar: scalar(128, 128),
                format: FloatingFormat::X87Extended80,
            },
            wchar_layout: integer(32, 32, Signedness::Signed),
            size_t_layout: integer(64, 64, Signedness::Unsigned),
            ptrdiff_t_layout: integer(64, 64, Signedness::Signed),
        },
        language_standard: LanguageStandard::C17,
        extension_profile: ExtensionProfile::new(ExtensionFamily::Gnu, []),
        compiler: toolchain.compiler_identity().clone(),
        sysroot: None,
        abi_flags: vec![NormalizedCompilerArg::try_new("-m64").expect("ABI flag")],
    })
    .expect("explicit H5 target")
}

fn scalar(storage_bits: u16, alignment_bits: u16) -> ScalarLayout {
    ScalarLayout {
        storage_bits,
        alignment_bits,
    }
}

fn integer(storage_bits: u16, alignment_bits: u16, signedness: Signedness) -> IntegerLayout {
    IntegerLayout {
        scalar: scalar(storage_bits, alignment_bits),
        signedness,
        representation: SignedIntegerRepresentation::TwosComplement,
    }
}

fn probe_limits() -> ProbeResourceLimits {
    ProbeResourceLimits::try_new(10_000, 512 * 1024 * 1024, 1024 * 1024, 16)
        .expect("H5 probe limits")
}

fn complete(
    source: &SourcePackage,
    roots: impl IntoIterator<Item = DeclarationId>,
) -> CompleteSourcePackage {
    source
        .clone()
        .into_complete(&Selection::only(roots).expect("nonempty H5 selection"))
        .expect("complete H5 source closure")
}

#[derive(Clone, Copy)]
enum Kind {
    Function,
    Variable,
    Record,
}

fn declaration_id(source: &SourcePackage, name: &str, kind: Kind) -> DeclarationId {
    source
        .declarations()
        .iter()
        .find(|declaration| {
            declaration
                .name
                .as_ref()
                .is_some_and(|value| value.normalized == name)
                && kind_matches(&declaration.kind, kind)
        })
        .unwrap_or_else(|| panic!("H5 declaration {name:?}"))
        .id
}

fn kind_matches(kind: &SourceDeclarationKind, expected: Kind) -> bool {
    match expected {
        Kind::Function => matches!(kind, SourceDeclarationKind::Function(_)),
        Kind::Variable => matches!(kind, SourceDeclarationKind::Variable(_)),
        Kind::Record => matches!(
            kind,
            SourceDeclarationKind::Record(value)
                if value.kind == parc::contract::RecordKind::Struct
        ),
    }
}

fn explicit_tool(variable: &str, fallback: &str) -> PathBuf {
    let supplied = std::env::var_os(variable).unwrap_or_else(|| OsString::from(fallback));
    canonical(Path::new(&supplied))
}

fn canonical(path: &Path) -> PathBuf {
    fs::canonicalize(path)
        .unwrap_or_else(|error| panic!("canonicalize {}: {error}", path.display()))
}

fn checked(command: &mut Command, action: &str) {
    let output = command
        .output()
        .unwrap_or_else(|error| panic!("{action}: {error}"));
    assert_success(output, action);
}

fn assert_success(output: Output, action: &str) {
    assert!(
        output.status.success(),
        "{action} failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

struct Scratch(PathBuf);

impl Scratch {
    fn new(prefix: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "{prefix}-{}-{}",
            std::process::id(),
            NEXT_SCRATCH.fetch_add(1, Ordering::Relaxed)
        ));
        assert!(!path.exists(), "H5 scratch path must be new");
        fs::create_dir(&path).expect("create H5 scratch directory");
        Self(canonical(&path))
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).expect("remove owned H5 scratch directory");
    }
}
