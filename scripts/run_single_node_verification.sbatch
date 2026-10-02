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
# Requires a cluster-approved rootless Docker daemon with cgroup v2/systemd.
# The reviewed host launcher sends a clean source snapshot to private Docker
# volumes. Repository code executes only in the offline container phase.
set -euo pipefail
cd "${SLURM_SUBMIT_DIR:?Submit from the repository directory}"
srun --ntasks=1 --cpu-bind=none python3 -I scripts/verify_container.py all \
  --cpus "${SLURM_CPUS_PER_TASK:-200}" --memory 1300g \
  --max-parallel 100 --jobs 2 --memory-percent 85

# Print a small untrusted-data receipt to the Slurm log. All reports/objects
# remain in the private volume; no repository scripts are executed on the host.
python3 -I scripts/verify_container.py report --report completion.json
