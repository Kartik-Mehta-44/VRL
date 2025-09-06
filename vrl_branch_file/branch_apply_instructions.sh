#!/usr/bin/env bash
set -euo pipefail
echo "This helper script assumes you are running it from the unzipped folder (that contains 'branch_files')"
if [ -z "${1:-}" ]; then
  BRANCH=experiments/setup
else
  BRANCH=$1
fi
echo "Creating branch $BRANCH in local repo (you must run this from your repo root)."
echo "COPY the following command and run it from your VRL repo root:"
cat <<EOF
git fetch origin
git checkout -b $BRANCH
cp -a $(pwd)/branch_files/. .
git add experiments .github README_apply_branch.txt branch_apply_instructions.sh
git commit -m "Add experiments folder, run_demo placeholder, CI skeleton, and issue templates"
git push -u origin $BRANCH
EOF
