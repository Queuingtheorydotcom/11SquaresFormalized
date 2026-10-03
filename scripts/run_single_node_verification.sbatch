#!/usr/bin/env bash
#SBATCH --job-name=eleven-square-verification
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=200
#SBATCH --mem=1300G
#SBATCH --time=3-00:00:00
#SBATCH --output=.verification/slurm-%j.log

# Submit from a persistent repository checkout; create .verification beforehand.
# Account, partition, allocation size and wall time are site-specific examples.
# Python, Lake and Lean run directly under the submitting user's permissions.
set -euo pipefail
cd "${SLURM_SUBMIT_DIR:?Submit from the repository directory}"
proof_python="${ELEVEN_SQUARE_PYTHON:-python3}"
"$proof_python" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 11) else "Python 3.11+ is required; set ELEVEN_SQUARE_PYTHON")'
export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
mkdir -p .verification

stop_file=".verification/STOP"
if [[ -e "$stop_file" ]]; then
  printf 'Remove %s before resuming verification.\n' "$stop_file" >&2
  exit 2
fi
setup_options=()
case "${ELEVEN_SQUARE_SETUP:-1}" in
  1) setup_options=(--setup) ;;
  0) ;;
  *) printf 'ELEVEN_SQUARE_SETUP must be 0 or 1.\n' >&2; exit 2 ;;
esac

srun --ntasks=1 --cpu-bind=none "$proof_python" -u scripts/verify.py \
  "${setup_options[@]}" --all --keep-going \
  --max-parallel "${ELEVEN_SQUARE_MAX_PARALLEL:-100}" \
  --jobs "${ELEVEN_SQUARE_JOBS:-2}" \
  --memory-percent "${ELEVEN_SQUARE_MEMORY_PERCENT:-85}" \
  --stop-file "$stop_file"

"$proof_python" -B scripts/finalize_verification.py --write

# A job-specific receipt avoids confusing an older success with this attempt.
receipt=".verification/completion-${SLURM_JOB_ID:?}.json"
"$proof_python" -B - "$receipt" <<'PY'
import hashlib
import json
import sys
from pathlib import Path

result = json.loads(Path('.verification/result.json').read_text())
audit = json.loads(Path('verification/wand125-upgrade.json').read_text())
required = (
    result.get('status') == 'OPTIMALITY_PROVED',
    result.get('global_optimality_proved') is True,
    audit.get('status') == 'OPTIMALITY_PROVED',
    audit.get('global_optimality_proved') is True,
    audit.get('full_upgrade_verified') is True,
    audit.get('explicit_native_admissions') == 0,
    audit.get('checked_modules') == result.get('checked_modules'),
)
if not all(required):
    raise SystemExit('Verification did not establish full optimality.')
completion = {
    'status': 'OPTIMALITY_PROVED',
    'global_optimality_proved': True,
    'full_upgrade_verified': True,
    'checked_modules': audit['checked_modules'],
    'lean_toolchain': audit['lean_toolchain'],
    'mathlib_revision': audit['mathlib_revision'],
    'audit_sha256': hashlib.sha256(Path('verification/wand125-upgrade.json').read_bytes()).hexdigest(),
    'manifest_sha256': hashlib.sha256(Path('MANIFEST.json').read_bytes()).hexdigest(),
}
Path(sys.argv[1]).write_text(json.dumps(completion, indent=2) + '\n')
print(f"COMPLETE: optimality verified; {audit['checked_modules']} local modules checked.")
print('Compact receipt: ' + sys.argv[1])
PY
