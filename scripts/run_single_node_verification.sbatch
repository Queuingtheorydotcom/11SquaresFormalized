#!/usr/bin/env bash
#SBATCH --job-name=eleven-square-verification
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=200
#SBATCH --mem=1300G
#SBATCH --time=3-00:00:00
#SBATCH --output=.verification/slurm-%j.log

# Submit from the prepared repository directory. Set your site's account and
# high-memory partition using sbatch options. Resource requests and wall time
# are examples, not predictions of completion time.
# Requires a cluster-approved rootless Docker daemon with cgroup v2/systemd.
# The reviewed host launcher sends a clean source snapshot to private Docker
# volumes. Repository code executes only in the offline container phase.
set -euo pipefail
cd "${SLURM_SUBMIT_DIR:?Submit from the repository directory}"
# RHEL 9's default python3 may be 3.9. Select an installed 3.11+ interpreter
# using ELEVEN_SQUARE_PYTHON=python3.11 (or your site's absolute module path).
proof_python="${ELEVEN_SQUARE_PYTHON:-python3}"
"$proof_python" -I -c 'import sys; sys.exit(0 if sys.version_info >= (3, 11) else "Host Python 3.11+ is required")'

# An administrator must have approved/accounted for this user daemon on the
# compute node. Opt in to starting the already installed systemd user service;
# this does not install Docker or configure Slurm cgroup delegation.
if [[ "${ELEVEN_SQUARE_START_USER_DOCKER:-0}" == 1 ]]; then
  export XDG_RUNTIME_DIR="${XDG_RUNTIME_DIR:-/run/user/$(id -u)}"
  export DBUS_SESSION_BUS_ADDRESS="${DBUS_SESSION_BUS_ADDRESS:-unix:path=$XDG_RUNTIME_DIR/bus}"
  systemctl --user start docker
fi
export DOCKER_CONTEXT="${ELEVEN_SQUARE_DOCKER_CONTEXT:-rootless}"
unset DOCKER_HOST
volume_options=()
if [[ -n "${ELEVEN_SQUARE_VOLUME:-}" ]]; then
  volume_options=(--volume "$ELEVEN_SQUARE_VOLUME")
fi
srun --ntasks=1 --cpu-bind=none "$proof_python" -I scripts/verify_container.py all \
  --cpus "${SLURM_CPUS_PER_TASK:-200}" --memory 1300g \
  --max-parallel 100 --jobs 2 --memory-percent 85 "${volume_options[@]}"

# Print a small untrusted-data receipt to the Slurm log. All reports/objects
# remain in the private volume; no repository scripts are executed on the host.
receipt=".verification/completion-${SLURM_JOB_ID:?}.json"
"$proof_python" -I scripts/verify_container.py report --report completion.json \
  "${volume_options[@]}" > "$receipt.tmp"
mv -- "$receipt.tmp" "$receipt"
printf 'Compact receipt: %s\n' "$receipt"
