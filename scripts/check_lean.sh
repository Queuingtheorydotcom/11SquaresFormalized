#!/usr/bin/env bash
# Check every included Lean module, preserving successful checks for later runs.
set -euo pipefail

repo_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"

for option in "$@"; do
  case "$option" in
    --setup|--fresh) ;;
    -h|--help)
      printf 'Usage: bash scripts/check_lean.sh [--setup] [--fresh]\n'
      printf '  --setup  Restore pinned proof sources, Lean, and dependency caches. Requires elan.\n'
      printf '  --fresh  Recheck everything instead of reusing matching successful checks.\n'
      exit 0
      ;;
    *) printf 'Unknown option: %s\n' "$option" >&2; exit 2 ;;
  esac
done

command -v python3 >/dev/null || { printf 'Python 3 is required.\n' >&2; exit 127; }
mkdir -p .verification
log_file="$repo_dir/.verification/check-$(date +%Y%m%d-%H%M%S)-$$.log"
printf 'Checking all Lean modules. Successful checks are saved for resuming.\nLog: %s\n' "$log_file"

set +e
python3 -u scripts/verify.py --all --keep-going "$@" 2>&1 | tee "$log_file"
statuses=("${PIPESTATUS[@]}")
set -e

if (( statuses[0] != 0 )); then
  printf '\nFAIL or interrupted (exit %s). See: %s\n' "${statuses[0]}" "$log_file" >&2
  exit "${statuses[0]}"
fi
if (( statuses[1] != 0 )); then
  printf '\nCould not save the complete log.\n' >&2
  exit "${statuses[1]}"
fi
printf '\nPASS: all included modules compile and the configured axiom audit passed.\n'
printf 'See the axiom result above and MISSING.md for the remaining proof obligations.\n'
printf 'Log: %s\n' "$log_file"
