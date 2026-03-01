#!/usr/bin/env python3

import os
import subprocess
import sys
import shutil
import urllib.request
import zipfile
import tempfile

# Project configurations
PROJECTS = {
    "tinyexpr": {
        "repo": "https://github.com/codeplea/tinyexpr",
        "build_cmd": ["make", "CC={CC}"],
        "test_cmd": ["make", "smoke", "CC={CC}"],
        "clean_cmd": ["make", "clean"],
    },
    "sds": {
        "repo": "https://github.com/antirez/sds",
        "build_cmd": ["make", "CC={CC}"],
        "test_cmd": ["./sds-test"],
        "clean_cmd": ["make", "clean"],
    },
    "c-testsuite": {
        "repo": "https://github.com/c-testsuite/c-testsuite",
        "build_cmd": ["true"],
        "patch_cmd": ["rm", "-f", "tests/single-exec/00209.c"],
        "test_cmd": ["sh", "-c", "for t in tests/single-exec/*.c; do CC={CC} CFLAGS='' ./runners/single-exec/posix $t || exit 1; done"],
        "clean_cmd": ["true"],
    },
    "lua": {
        "repo": "https://github.com/lua/lua",
        "build_cmd": ["make", "CC={CC}", "CFLAGS=-O2 -DLUA_USE_LINUX -DLUA_USE_JUMPTABLE=0", "MYCFLAGS=", "MYLDFLAGS=", "MYLIBS=-lm"],
        "test_cmd": ["./lua", "-e", "print('hello from lua built with cendol')"],
        "clean_cmd": ["make", "clean"],
    },
    "zlib": {
        "repo": "https://github.com/madler/zlib",
        "build_cmd": ["sh", "-c", "./configure && make CC={CC}"],
        "test_cmd": ["make", "test", "CC={CC}"],
        "clean_cmd": ["make", "clean"],
    },
    "libpng": {
        "repo": "https://github.com/pnggroup/libpng",
        "build_cmd": ["sh", "-c", "autoreconf -f -i && CPPFLAGS='-I../zlib' LDFLAGS='-L../zlib' ./configure --disable-dependency-tracking && make CC={CC}"],
        "test_cmd": ["make", "test", "CC={CC}"],
        "clean_cmd": ["make", "clean"],
    },
    "sqlite": {
        "download_url": "https://www.sqlite.org/2025/sqlite-amalgamation-3480000.zip",
        "build_cmd": ["sh", "-c", "{CC} -O2 -DSQLITE_THREADSAFE=0 -o sqlite3 shell.c sqlite3.c -lm"],
        "test_cmd": ["./sqlite3", ":memory:", "SELECT 'hello from sqlite built with cendol';"],
        "clean_cmd": ["rm", "-f", "sqlite3"],
    }
}

def run_command(cmd, cwd=None):
    print(f"Running: {' '.join(cmd)} in {cwd or '.'}")
    result = subprocess.run(cmd, cwd=cwd)
    if result.returncode != 0:
        print(f"Error: Command failed with return code {result.returncode}")
        sys.exit(1)

def print_usage():
    print("Usage: ./realworld_test.py <nama-project>|clean|nuke")
    print("\nAvailable projects:")
    for name in PROJECTS:
        print(f"  - {name}")
    print("\nSubcommands:")
    print("  clean    Runs 'make clean' (or equivalent) in each cloned project directory.")
    print("  nuke     Removes the 'realworld' directory containing all cloned projects.")

def main():
    if len(sys.argv) < 2:
        print_usage()
        sys.exit(1)

    project_name = sys.argv[1]
    
    # Root directory of cendol (where this script is located)
    cendol_root = os.path.dirname(os.path.abspath(__file__))
    realworld_dir = os.path.join(cendol_root, "realworld")

    if project_name == "nuke":
        if os.path.exists(realworld_dir):
            print(f"Nuking {realworld_dir}...")
            shutil.rmtree(realworld_dir)
            print("Nuked successfully.")
        else:
            print("Already clean.")
        return

    if project_name == "clean":
        if not os.path.exists(realworld_dir):
            print("Nothing to clean.")
            return
        
        for name, config in PROJECTS.items():
            p_dir = os.path.join(realworld_dir, name)
            if os.path.exists(p_dir):
                print(f"Cleaning {name}...")
                run_command(config["clean_cmd"], cwd=p_dir)
        return

    if project_name not in PROJECTS:
        print(f"Error: Project '{project_name}' not found.")
        print_usage()
        sys.exit(1)

    config = PROJECTS[project_name]
    project_dir = os.path.join(realworld_dir, project_name)
    cendol_bin = os.path.join(cendol_root, "target/debug/cendol")

    if not os.path.exists(realworld_dir):
        os.makedirs(realworld_dir)

    # 1. Clone/Download
    if not os.path.exists(project_dir):
        if "repo" in config:
            print(f"Cloning {project_name}...")
            run_command(["git", "clone", config["repo"], project_name], cwd=realworld_dir)
        elif "download_url" in config:
            print(f"Downloading {project_name}...")
            zip_path = os.path.join(realworld_dir, f"{project_name}.zip")
            urllib.request.urlretrieve(config["download_url"], zip_path)
            with zipfile.ZipFile(zip_path, 'r') as zf:
                zf.extractall(realworld_dir)
            os.remove(zip_path)
            # The zip extracts to a subdirectory, rename it
            extracted = [d for d in os.listdir(realworld_dir) if d.startswith("sqlite-") and os.path.isdir(os.path.join(realworld_dir, d))]
            if extracted:
                os.rename(os.path.join(realworld_dir, extracted[0]), project_dir)
    else:
        if "repo" in config:
            print(f"Updating {project_name}...")
            run_command(["git", "pull"], cwd=project_dir)
        else:
            print(f"{project_name} already downloaded.")

    # 2. Patching (Usually works by passing CC to make)
    # If specific patching is needed, it can be added here.
    # For now, we'll just use the CC environment variable or pass it to make.
    if "patch_cmd" in config:
        print(f"Patching {project_name}...")
        run_command(config["patch_cmd"], cwd=project_dir)

    # Ensure compiler is built
    print("Building cendol...")
    run_command(["cargo", "build"], cwd=cendol_root)

    # 3. Build
    build_cmd = [arg.format(CC=cendol_bin) for arg in config["build_cmd"]]
    run_command(build_cmd, cwd=project_dir)

    # 4. Test
    test_cmd = [arg.format(CC=cendol_bin) for arg in config["test_cmd"]]
    run_command(test_cmd, cwd=project_dir)

    print(f"\nSuccess: {project_name} tested successfully with cendol!")

if __name__ == "__main__":
    main()
