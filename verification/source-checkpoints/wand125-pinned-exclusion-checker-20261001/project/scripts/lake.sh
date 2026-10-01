#!/usr/bin/env bash
# Run Lake with the project's pinned Lean toolchain, from any working directory.
set -euo pipefail
task_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$task_root"
task_toolchain="$(tr -d '\r\n' < lean-toolchain)"
if command -v elan >/dev/null 2>&1; then
  task_elan="$(command -v elan)"
elif [[ -x "$HOME/.elan/bin/elan" ]]; then
  task_elan="$HOME/.elan/bin/elan"
else
  printf '%s\n' 'Elan was not found. Install Lean through https://lean-lang.org/install/ and retry.' >&2
  exit 1
fi
exec "$task_elan" run "$task_toolchain" lake "$@"
