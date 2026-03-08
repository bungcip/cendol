#!/usr/bin/env python3

import argparse
import json
import os
import signal
import shutil
import subprocess
import tempfile
import time
from pathlib import Path


def parse_args():
    parser = argparse.ArgumentParser(
        description=(
            "Generate random Csmith programs and check for behavior mismatches "
            "between cendol and reference compilers (clang/gcc)."
        )
    )
    parser.add_argument(
        "--csmith",
        default="/usr/local/bin/csmith",
        help="Path to csmith binary.",
    )
    parser.add_argument(
        "--cendol",
        default="./target/debug/cendol",
        help="Path to cendol compiler.",
    )
    parser.add_argument(
        "--refs",
        default="clang,gcc",
        help="Comma-separated reference compilers (names in PATH or explicit paths).",
    )
    parser.add_argument(
        "--include",
        action="append",
        default=[
            "/home/bungcip/csmith/runtime",
            "/home/bungcip/csmith/build/runtime",
        ],
        help="Additional include directory. Can be passed multiple times.",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=os.cpu_count() or 1,
        help="Number of parallel workers (default: all CPU cores).",
    )
    parser.add_argument(
        "--tests",
        type=int,
        default=0,
        help="Number of test cases to run (0 means infinite).",
    )
    parser.add_argument(
        "--seed-start",
        type=int,
        default=int(time.time()),
        help="Starting seed value.",
    )
    parser.add_argument(
        "--compile-timeout",
        type=float,
        default=20.0,
        help="Per-compiler compile timeout in seconds.",
    )
    parser.add_argument(
        "--run-timeout",
        type=float,
        default=10.0,
        help="Per-program runtime timeout in seconds.",
    )
    parser.add_argument(
        "--out-dir",
        default="csmith-diff-results",
        help="Output directory for findings and logs.",
    )
    parser.add_argument(
        "--keep-all",
        action="store_true",
        help="Keep temporary directories for non-divergent cases.",
    )
    parser.add_argument(
        "--continue-on-divergence",
        action="store_true",
        help="Continue fuzzing after divergence (default: stop on first divergence).",
    )
    return parser.parse_args()


def resolve_compiler(name_or_path):
    if "/" in name_or_path:
        p = Path(name_or_path).expanduser()
        if p.exists():
            return str(p.resolve())
        return None
    return shutil.which(name_or_path)


def run_cmd(cmd, timeout, cwd=None):
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
            cwd=cwd,
        )
        return {
            "ok": True,
            "timed_out": False,
            "returncode": proc.returncode,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
        }
    except subprocess.TimeoutExpired as ex:
        return {
            "ok": False,
            "timed_out": True,
            "returncode": None,
            "stdout": ex.stdout if isinstance(ex.stdout, str) else "",
            "stderr": ex.stderr if isinstance(ex.stderr, str) else "",
        }


def write_json(path, data):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, sort_keys=True)


def run_one_case(
    seed,
    csmith_path,
    include_dirs,
    compiler_map,
    compile_timeout,
    run_timeout,
    work_root,
    divergence_root,
    keep_all,
):
    case_dir = Path(tempfile.mkdtemp(prefix=f"seed_{seed}_", dir=work_root))
    src = case_dir / "test.c"
    case_meta = {
        "seed": seed,
        "source": str(src),
        "generation": {},
        "compile": {},
        "run": {},
        "divergence": None,
    }

    csmith_cmd = [csmith_path, "--seed", str(seed)]
    with open(src, "w", encoding="utf-8") as out_f:
        csmith_res = run_cmd(csmith_cmd, timeout=compile_timeout)
        case_meta["generation"] = {
            "cmd": csmith_cmd,
            **csmith_res,
        }
        if csmith_res["timed_out"] or csmith_res["returncode"] != 0:
            write_json(case_dir / "result.json", case_meta)
            if keep_all:
                return {
                    "seed": seed,
                    "status": "skipped",
                    "reason": "generation_failure",
                    "artifact_dir": str(case_dir),
                }
            shutil.rmtree(case_dir, ignore_errors=True)
            return {
                "seed": seed,
                "status": "skipped",
                "reason": "generation_failure",
            }
        out_f.write(csmith_res["stdout"])

    include_flags = [f"-I{d}" for d in include_dirs]
    for compiler_name, compiler_path in compiler_map.items():
        exe_path = case_dir / f"{compiler_name}.out"
        compile_cmd = [compiler_path, str(src), "-o", str(exe_path)] + include_flags
        compile_res = run_cmd(compile_cmd, timeout=compile_timeout, cwd=case_dir)
        case_meta["compile"][compiler_name] = {
            "cmd": compile_cmd,
            **compile_res,
        }
        if compile_res["ok"] and compile_res["returncode"] == 0:
            run_res = run_cmd([str(exe_path)], timeout=run_timeout, cwd=case_dir)
            case_meta["run"][compiler_name] = run_res

    cendol_comp = case_meta["compile"]["cendol"]
    cendol_run = case_meta["run"].get("cendol")
    ref_names = [name for name in compiler_map if name != "cendol"]

    divergence = None

    for ref in ref_names:
        ref_comp = case_meta["compile"][ref]
        ref_run = case_meta["run"].get(ref)

        cendol_compiled = cendol_comp["ok"] and cendol_comp["returncode"] == 0
        ref_compiled = ref_comp["ok"] and ref_comp["returncode"] == 0

        if cendol_compiled != ref_compiled:
            divergence = {
                "type": "compile_mismatch",
                "against": ref,
                "cendol_compiled": cendol_compiled,
                "ref_compiled": ref_compiled,
            }
            break

        if cendol_compiled and ref_compiled:
            # Only compare terminating runs. Timeout-only differences are not
            # considered divergences.
            if not cendol_run or not ref_run:
                continue
            if cendol_run["timed_out"] or ref_run["timed_out"]:
                continue

            cendol_tuple = (
                cendol_run["returncode"],
                cendol_run["stdout"],
                cendol_run["stderr"],
            )
            ref_tuple = (
                ref_run["returncode"],
                ref_run["stdout"],
                ref_run["stderr"],
            )
            if cendol_tuple != ref_tuple:
                divergence = {
                    "type": "runtime_mismatch",
                    "against": ref,
                    "cendol": {
                        "returncode": cendol_run["returncode"],
                        "timed_out": cendol_run["timed_out"],
                    },
                    "ref": {
                        "returncode": ref_run["returncode"],
                        "timed_out": ref_run["timed_out"],
                    },
                }
                break

    if divergence:
        case_meta["divergence"] = divergence
        write_json(case_dir / "result.json", case_meta)
        dest = Path(divergence_root) / f"seed_{seed}_{divergence['type']}"
        if dest.exists():
            dest = Path(divergence_root) / f"seed_{seed}_{divergence['type']}_{int(time.time() * 1000)}"
        shutil.move(str(case_dir), str(dest))
        return {
            "seed": seed,
            "status": "divergence",
            "type": divergence["type"],
            "against": divergence.get("against"),
            "artifact_dir": str(dest),
        }

    write_json(case_dir / "result.json", case_meta)
    if keep_all:
        return {"seed": seed, "status": "ok", "artifact_dir": str(case_dir)}

    shutil.rmtree(case_dir, ignore_errors=True)
    return {"seed": seed, "status": "ok"}


def run_one_case_child(
    seed,
    summary_path,
    csmith_path,
    include_dirs,
    compiler_map,
    compile_timeout,
    run_timeout,
    work_root,
    divergence_root,
    keep_all,
):
    try:
        result = run_one_case(
            seed=seed,
            csmith_path=csmith_path,
            include_dirs=include_dirs,
            compiler_map=compiler_map,
            compile_timeout=compile_timeout,
            run_timeout=run_timeout,
            work_root=work_root,
            divergence_root=divergence_root,
            keep_all=keep_all,
        )
    except Exception as exn:
        result = {
            "seed": seed,
            "status": "error",
            "error": str(exn),
        }
    write_json(summary_path, result)


def terminate_children(children):
    pids = list(children.keys())

    def signal_tree(pid, sig):
        # Each worker runs in its own process group (pgid==pid), so signal
        # the group first to include compiler/runtime subprocesses.
        try:
            os.killpg(pid, sig)
            return
        except ProcessLookupError:
            pass
        except OSError:
            pass
        try:
            os.kill(pid, sig)
        except ProcessLookupError:
            pass
        except OSError:
            pass

    for pid in pids:
        signal_tree(pid, signal.SIGTERM)

    deadline = time.time() + 2.0
    remaining = set(pids)
    while remaining and time.time() < deadline:
        for pid in list(remaining):
            try:
                done, _ = os.waitpid(pid, os.WNOHANG)
                if done == pid:
                    remaining.remove(pid)
            except ChildProcessError:
                remaining.remove(pid)
            except OSError:
                remaining.remove(pid)
        if remaining:
            time.sleep(0.05)

    for pid in list(remaining):
        signal_tree(pid, signal.SIGKILL)

    for pid in list(remaining):
        try:
            os.waitpid(pid, 0)
        except ChildProcessError:
            pass
        except OSError:
            pass


def main():
    args = parse_args()

    csmith = resolve_compiler(args.csmith)
    if not csmith:
        raise SystemExit(f"error: csmith not found: {args.csmith}")

    cendol = resolve_compiler(args.cendol)
    if not cendol:
        raise SystemExit(f"error: cendol not found: {args.cendol}")

    refs = [x.strip() for x in args.refs.split(",") if x.strip()]
    if not refs:
        raise SystemExit("error: at least one reference compiler is required")

    compiler_map = {"cendol": cendol}
    missing_refs = []
    for ref in refs:
        resolved = resolve_compiler(ref)
        if not resolved:
            missing_refs.append(ref)
            continue
        key = Path(ref).name if "/" in ref else ref
        if key == "cendol":
            key = "ref_cendol"
        compiler_map[key] = resolved

    if len(compiler_map) == 1:
        raise SystemExit(
            f"error: no usable reference compilers found in --refs={args.refs!r}"
        )

    out_dir = Path(args.out_dir).resolve()
    work_root = out_dir / "work"
    divergence_root = out_dir / "divergences"
    out_dir.mkdir(parents=True, exist_ok=True)
    work_root.mkdir(parents=True, exist_ok=True)
    divergence_root.mkdir(parents=True, exist_ok=True)

    config = {
        "csmith": csmith,
        "compilers": compiler_map,
        "include_dirs": args.include,
        "jobs": args.jobs,
        "tests": args.tests,
        "seed_start": args.seed_start,
        "compile_timeout": args.compile_timeout,
        "run_timeout": args.run_timeout,
        "keep_all": args.keep_all,
        "continue_on_divergence": args.continue_on_divergence,
        "missing_refs": missing_refs,
        "out_dir": str(out_dir),
    }
    write_json(out_dir / "run_config.json", config)
    print(json.dumps(config, indent=2, sort_keys=True))

    max_workers = max(1, args.jobs)
    total_target = args.tests
    total_done = 0
    divergences = 0
    skipped = 0
    seed_next = args.seed_start

    stop = False
    in_flight = {}

    def can_submit_more():
        if total_target == 0:
            return True
        return (seed_next - args.seed_start) < total_target

    try:
        while not stop:
            while len(in_flight) < max_workers and can_submit_more():
                seed = seed_next
                seed_next += 1
                summary_path = work_root / f"seed_{seed}.summary.json"
                pid = os.fork()
                if pid == 0:
                    # Give each worker a dedicated process group so parent-side
                    # cleanup can reliably kill the worker and all descendants.
                    try:
                        os.setsid()
                    except OSError:
                        pass
                    run_one_case_child(
                        seed=seed,
                        summary_path=str(summary_path),
                        csmith_path=csmith,
                        include_dirs=args.include,
                        compiler_map=compiler_map,
                        compile_timeout=args.compile_timeout,
                        run_timeout=args.run_timeout,
                        work_root=str(work_root),
                        divergence_root=str(divergence_root),
                        keep_all=args.keep_all,
                    )
                    os._exit(0)
                in_flight[pid] = {"seed": seed, "summary_path": summary_path}

            if not in_flight:
                break

            pid, _status = os.waitpid(-1, 0)
            info = in_flight.pop(pid, None)
            if info is None:
                continue

            seed = info["seed"]
            summary_path = info["summary_path"]
            if summary_path.exists():
                with open(summary_path, "r", encoding="utf-8") as f:
                    res = json.load(f)
                summary_path.unlink(missing_ok=True)
            else:
                res = {"seed": seed, "status": "error", "error": "missing summary"}

            total_done += 1
            if res["status"] == "divergence":
                divergences += 1
                print(
                    f"[seed {seed}] DIVERGENCE {res.get('type')} "
                    f"(against={res.get('against')}) artifacts={res.get('artifact_dir')}"
                )
                if not args.continue_on_divergence:
                    stop = True
            elif res["status"] == "error":
                divergences += 1
                print(f"[seed {seed}] internal error: {res.get('error')}")
                if not args.continue_on_divergence:
                    stop = True
            elif res["status"] == "skipped":
                skipped += 1
            elif total_done % 10 == 0:
                print(
                    f"[progress] completed={total_done} divergences={divergences} skipped={skipped}"
                )

            if total_target and total_done >= total_target:
                stop = True
    except KeyboardInterrupt:
        stop = True
    finally:
        terminate_children(in_flight)

    print(
        f"done: completed={total_done} divergences={divergences} skipped={skipped} "
        f"results_dir={out_dir}"
    )


if __name__ == "__main__":
    main()
