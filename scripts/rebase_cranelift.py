#!/usr/bin/env python3
import os
import sys
import subprocess
import shutil
import argparse

# Path to the local Cranelift fork
LOCAL_CRANELIFT_DIR = "crates/cranelift"
VERSION_FILE = os.path.join(LOCAL_CRANELIFT_DIR, "UPSTREAM_VERSION")

def run_command(cmd, cwd=None, check=True):
    print(f"Running: {' '.join(cmd)}")
    res = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if check and res.returncode != 0:
        print(f"Error executing command: {' '.join(cmd)}")
        print(f"Stdout:\n{res.stdout}")
        print(f"Stderr:\n{res.stderr}")
        sys.exit(res.returncode)
    return res

def get_current_upstream_version():
    if not os.path.exists(VERSION_FILE):
        print(f"Error: Upstream version file not found at {VERSION_FILE}")
        sys.exit(1)
    with open(VERSION_FILE, "r") as f:
        return f.read().strip()

def main():
    parser = argparse.ArgumentParser(description="Rebase Cendol's local Cranelift fork to a new upstream Wasmtime version.")
    parser.add_argument("target_version", help="The target upstream Wasmtime tag (e.g., v47.0.0)")
    args = parser.parse_args()

    target_version = args.target_version
    base_version = get_current_upstream_version()
    
    print(f"Rebasing Cranelift fork from {base_version} to {target_version}...")

    temp_dir = "/tmp/cranelift_rebase"
    if os.path.exists(temp_dir):
        shutil.rmtree(temp_dir)
    os.makedirs(temp_dir)

    base_clone_dir = os.path.join(temp_dir, "wasmtime_base")
    target_clone_dir = os.path.join(temp_dir, "wasmtime_target")
    patch_file = os.path.join(temp_dir, "our_changes.patch")

    try:
        # 1. Clone base version to extract unmodified upstream base cranelift
        print(f"Cloning upstream wasmtime at base version {base_version}...")
        run_command([
            "git", "clone", "--depth", "1", "--branch", base_version,
            "https://github.com/bytecodealliance/wasmtime.git", base_clone_dir
        ])

        # 2. Clone target version to extract unmodified upstream target cranelift
        print(f"Cloning upstream wasmtime at target version {target_version}...")
        run_command([
            "git", "clone", "--depth", "1", "--branch", target_version,
            "https://github.com/bytecodealliance/wasmtime.git", target_clone_dir
        ])

        # 3. Generate patch of our changes
        print("Generating diff of our local modifications...")
        # git diff --no-index returns 1 if there are differences, so we don't check exit code here
        diff_res = run_command([
            "git", "diff", "--no-index",
            os.path.join(base_clone_dir, "cranelift"),
            LOCAL_CRANELIFT_DIR
        ], check=False)
        
        if diff_res.returncode == 0:
            print("No local changes detected in the fork. Just updating upstream source...")
            has_changes = False
        else:
            has_changes = True
            with open(patch_file, "w") as f:
                f.write(diff_res.stdout)
            print(f"Diff saved to {patch_file}")

        # 4. Replace local Cranelift directory with target upstream cranelift
        print(f"Replacing local {LOCAL_CRANELIFT_DIR} with {target_version} upstream...")
        if os.path.exists(LOCAL_CRANELIFT_DIR):
            # Keep the UPSTREAM_VERSION file path valid
            shutil.rmtree(LOCAL_CRANELIFT_DIR)
        shutil.copytree(os.path.join(target_clone_dir, "cranelift"), LOCAL_CRANELIFT_DIR)

        # 5. Apply the generated patch of our changes
        if has_changes:
            print("Applying local modifications patch...")
            # We use git apply with --directory to apply the diff to the newly copied directory
            apply_res = run_command([
                "git", "apply", "--reject", "--whitespace=nowarn", patch_file
            ], check=False)
            
            if apply_res.returncode != 0:
                print("\n[WARNING] Some patch chunks failed to apply cleanly!")
                print("Merge conflicts were generated. Please resolve any '.rej' files in crates/cranelift/")
                print(apply_res.stderr)
            else:
                print("Patch applied cleanly!")

        # 6. Update the UPSTREAM_VERSION file
        with open(VERSION_FILE, "w") as f:
            f.write(target_version + "\n")
        print(f"Successfully updated UPSTREAM_VERSION to {target_version}")

    finally:
        # Cleanup
        print("Cleaning up temporary directories...")
        if os.path.exists(temp_dir):
            shutil.rmtree(temp_dir)
            
    print("Rebase script complete.")

if __name__ == "__main__":
    main()
