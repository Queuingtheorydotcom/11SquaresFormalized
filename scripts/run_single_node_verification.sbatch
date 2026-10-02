#!/usr/bin/env bash
#SBATCH --job-name=eleven-square-verification
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=200
#SBATCH --mem=1300G
#SBATCH --time=24:00:00
#SBATCH --output=.verification/slurm-%j.log

# Submit from the prepared repository directory. Set your site's account and
# high-memory partition using sbatch options. Resource requests and wall time
# are examples, not predictions of completion time.
set -euo pipefail
if [[ "${ELEVEN_SQUARE_ALLOW_HOST_EXECUTION:-}" != 1 ]]; then
  echo 'REFUSED: this example does not sandbox Python, Lake, or Lean. See SECURITY.md.' >&2
  echo 'Use a validated isolation boundary; the acknowledgement flag does not create one.' >&2
  exit 2
fi
cd "${SLURM_SUBMIT_DIR:?Submit from the repository directory}"
export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"

srun --ntasks=1 --cpu-bind=none python3 -u scripts/verify.py \
  --setup --all --keep-going \
  --max-parallel 100 --jobs 2 --memory-percent 85

python3 -B scripts/finalize_verification.py --write

python3 -B - <<'PY'
import hashlib
import json
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
Path('.verification/completion.json').write_text(json.dumps(completion, indent=2) + '\n')
print(f"COMPLETE: optimality verified; {audit['checked_modules']} local modules checked.")
print('Compact receipt: .verification/completion.json')
PY
