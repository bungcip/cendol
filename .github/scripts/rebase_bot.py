import os
import subprocess
import sys


def run(cmd: str):
    print(f"+ {cmd}")
    subprocess.run(cmd, shell=True, check=True)


def main():
    base = os.environ["BASE_BRANCH"]
    head = os.environ["HEAD_BRANCH"]

    run("git config user.name 'github-actions[bot]'")
    run("git config user.email '41898282+github-actions[bot]@users.noreply.github.com'")

    # Fetch base branch
    run(f"git fetch origin {base}")

    # Rebase
    try:
        run(f"git rebase origin/{base}")
    except subprocess.CalledProcessError:
        print("❌ Rebase conflict, aborting")
        run("git rebase --abort")
        sys.exit(1)

    # Run cargo fmt
    run("cargo fmt")

    # Commit fmt changes if any
    status = subprocess.check_output("git status --porcelain", shell=True).decode().strip()
    if status:
        run("git add .")
        run("git commit -m 'chore: cargo fmt'")
    else:
        print("✔ No formatting changes")

    # Force push back to PR branch
    run(f"git push origin HEAD:{head} --force-with-lease")

    print("✅ Rebase & format completed")


if __name__ == "__main__":
    main()
