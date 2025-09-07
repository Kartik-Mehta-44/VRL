HOW TO APPLY THESE FILES INTO YOUR LOCAL VRL GIT REPO (step-by-step)

1. Download and unzip the provided archive into a temporary folder.
2. `cd` into your local VRL repository root.
3. Create and switch to a new branch (recommended name `experiments/setup`):
   ```
   git fetch origin
   git checkout -b experiments/setup
   ```
4. Copy files from the unzipped `branch_files` into your repository root. From the unzip location:
   ```
   cp -a branch_files/. /path/to/VRL/
   ```
   or on Windows use Explorer to move the files.
5. Stage, commit, and push:
   ```
   git add experiments .github README_apply_branch.txt branch_apply_instructions.sh
   git commit -m "Add experiments folder, run_demo placeholder, CI skeleton, and issue templates"
   git push -u origin experiments/setup
   ```
6. Open the repository in VS Code (it will keep the current branch):
   ```
   code /path/to/VRL
   ```
   or from inside the repo:
   ```
   code .
   ```
7. Create a PR on GitHub (web UI) or using the GitHub CLI:
   ```
   gh pr create --fill
   ```
