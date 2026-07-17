use cendol::driver::CompilerDriver;
use cendol::driver::artifact::CompilePhase;
use cendol::driver::cli::parse_args_from;
use criterion::{Criterion, criterion_group, criterion_main};
use std::path::Path;
use std::process::Command;
use std::time::Duration;

const SQLITE_PATH: &str = "realworld/sqlite/sqlite3.c";

fn prepare_sqlite() {
    if !Path::new(SQLITE_PATH).exists() {
        println!("Preparing sqlite source...");
        let status = Command::new("python3")
            .arg("realworld_test.py")
            .arg("prepare")
            .arg("sqlite")
            .status()
            .expect("Failed to execute realworld_test.py");

        if !status.success() {
            panic!("Failed to prepare sqlite source");
        }
    }
}

fn bench_compiler_stages(c: &mut Criterion) {
    prepare_sqlite();

    let mut group = c.benchmark_group("compiler_stages");
    group.sample_size(30);
    group.warm_up_time(Duration::from_secs(5));
    group.measurement_time(Duration::from_secs(20));

    let run_stage = |b: &mut criterion::Bencher, phase: CompilePhase| {
        b.iter(|| {
            let args = vec![
                "cendol",
                "-I",
                "realworld/sqlite",
                "-DSQLITE_THREADSAFE=0",
                "--max-include-depth",
                "100",
                SQLITE_PATH,
            ];
            let config = parse_args_from(args.into_iter().map(String::from)).unwrap();
            let mut driver = CompilerDriver::from_config(config);
            let _ = driver.run_pipeline(phase);
        })
    };

    group.bench_function("preprocess_sqlite", |b| run_stage(b, CompilePhase::Preprocess));
    group.bench_function("parse_sqlite", |b| run_stage(b, CompilePhase::Parse));
    group.bench_function("analyze_sqlite", |b| run_stage(b, CompilePhase::Mir));
    group.bench_function("codegen_sqlite", |b| run_stage(b, CompilePhase::Cranelift));

    group.finish();
}

criterion_group!(benches, bench_compiler_stages);
criterion_main!(benches);
