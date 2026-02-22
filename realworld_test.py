#!/usr/bin/env python3

import os
import subprocess
import sys
import shutil

# Project configurations
PROJECTS = {
    "tinyexpr": {
        "repo": "https://github.com/codeplea/tinyexpr",
        "build_cmd": ["make", "CC={CC}"],
        "test_cmd": ["make", "smoke", "CC={CC}"],
    },
    "sds": {
        "repo": "https://github.com/antirez/sds",
        "build_cmd": ["make", "CC={CC}"],
        "test_cmd": ["./sds-test"],
    },
    "c-testsuite": {
        "repo": "https://github.com/c-testsuite/c-testsuite",
        "build_cmd": ["true"],
        "test_cmd": ["sh", "-c", "for t in tests/single-exec/*.c; do if [ \"$t\" = \"tests/single-exec/00204.c\" ]; then continue; fi; CC={CC} CFLAGS='' ./runners/single-exec/posix $t || exit 1; done"],
    },
    "lua": {
        "repo": "https://github.com/lua/lua",
        "build_cmd": ["make", "CC={CC}", "CFLAGS=-O2 -DLUA_USE_LINUX", "MYCFLAGS=", "MYLDFLAGS=", "MYLIBS=-lm"],
        "test_cmd": ["./lua", "-e", "print('hello from lua built with cendol')"],
    }
}

def run_command(cmd, cwd=None):
    print(f"Running: {' '.join(cmd)} in {cwd or '.'}")
    result = subprocess.run(cmd, cwd=cwd)
    if result.returncode != 0:
        print(f"Error: Command failed with return code {result.returncode}")
        sys.exit(1)

def print_usage():
    print("Usage: ./realworld_test.py <nama-project>|clean")
    print("\nAvailable projects:")
    for name in PROJECTS:
        print(f"  - {name}")
    print("\nSubcommands:")
    print("  clean    Removes the 'realworld' directory containing all cloned projects.")

def main():
    if len(sys.argv) < 2:
        print_usage()
        sys.exit(1)

    project_name = sys.argv[1]
    
    # Root directory of cendol (where this script is located)
    cendol_root = os.path.dirname(os.path.abspath(__file__))
    realworld_dir = os.path.join(cendol_root, "realworld")

    if project_name == "clean":
        if os.path.exists(realworld_dir):
            print(f"Cleaning {realworld_dir}...")
            shutil.rmtree(realworld_dir)
            print("Cleaned successfully.")
        else:
            print("Already clean.")
        return

    if project_name not in PROJECTS:
        print(f"Error: Project '{project_name}' not found.")
        print_usage()
        sys.exit(1)

    config = PROJECTS[project_name]
    repo_url = config["repo"]
    project_dir = os.path.join(realworld_dir, project_name)
    cendol_bin = os.path.join(cendol_root, "target/debug/cendol")

    if not os.path.exists(realworld_dir):
        os.makedirs(realworld_dir)

    # 1. Clone or Pull
    if not os.path.exists(project_dir):
        print(f"Cloning {project_name}...")
        run_command(["git", "clone", repo_url, project_name], cwd=realworld_dir)
    else:
        print(f"Updating {project_name}...")
        run_command(["git", "pull"], cwd=project_dir)

    # 2. Patching (Usually works by passing CC to make)
    # If specific patching is needed, it can be added here.
    # For now, we'll just use the CC environment variable or pass it to make.

    # 3. Build
    build_cmd = [arg.format(CC=cendol_bin) for arg in config["build_cmd"]]
    run_command(build_cmd, cwd=project_dir)

    # 4. Test
    test_cmd = [arg.format(CC=cendol_bin) for arg in config["test_cmd"]]
    run_command(test_cmd, cwd=project_dir)

    print(f"\nSuccess: {project_name} tested successfully with cendol!")

if __name__ == "__main__":
    main()
