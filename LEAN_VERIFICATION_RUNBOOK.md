# RHEL 9.6 / Slurm: complete eleven-square verification

Updated 2026-10-03. This guide is part of the Formalized repository and describes
running directly on one shared-cluster node. No container runtime is used.
It assumes the checked-out proof repository, official Lean/Lake, mathlib and
its dependencies/downloads are trusted; see [SECURITY.md](SECURITY.md).
No packing search, external algebra system or third-party Python package is
needed. Full replay runtime, peak RAM and final disk usage are unmeasured;
the examples below request one-day allocations and allow resuming later.

Repository: https://github.com/Queuingtheorydotcom/11SquaresFormalized.git
Branch: `codex/simplification-verifier-20261003`
Simplified proof checkpoint: `34e6b03536469379445bc7f87119cbb06d118f77`
Verifier branch merged at: `5f03579427807e9d199bff215c0bb08bac459d76`
Lean: `leanprover/lean4:v4.34.1`
mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`

Use the branch after the updated launcher and this guide have been pushed.

## 1. Fresh account and prerequisites

Obtain a normal cluster login, SSH access, an authorized Slurm account and a
partition permitting one node with about 192 physical cores and 1,400 GiB RAM. The example
reserves 1,300 GiB. Replace `YOUR_ACCOUNT` and `YOUR_PARTITION` below with the
site's actual values. The site supplies Slurm itself.

Use persistent storage visible from login and compute nodes. The checkout,
tracked sources, dependencies and checkpoints must survive allocation loss.
Node-local ephemeral scratch cannot provide that guarantee. Allow generous disk
space and inode capacity: the reported optimality source closure is about
1.09 GB in 6,326 local modules, before Git history, other local modules, Lean,
mathlib, compiled objects and logs. Final disk requirements are unknown.
The simplified Lean files are tracked; no historical proof archives are restored.
The full-tree preflight counts 7,906 local modules, including modules outside
the 6,326-module optimality closure. The launcher checks the full local tree.

Required tools: Bash, Git, curl, CA certificates, Python **3.11 or newer**, and
elan (installed below in your account). RHEL 9's default `python3` may be 3.9;
use `python3.11` explicitly or the site's equivalent module/path. An administrator
can install the base packages; ordinary users should use provided packages/modules:

```bash
sudo dnf install -y python3.11 git curl ca-certificates
```

There is no pip installation. If Python requires a site module on compute
nodes, follow the site's procedure and export `ELEVEN_SQUARE_PYTHON` as the
interpreter's absolute compute-visible path. Check:

```bash
python3.11 --version
git --version
curl --version
sbatch --version
```

[Red Hat's Python installation documentation](https://docs.redhat.com/en/documentation/red_hat_enterprise_linux/9/html/installing_and_using_dynamic_programming_languages/assembly_installing-and-using-python_installing-and-using-dynamic-programming-languages).

## 2. Install elan as the ordinary user

Skip this if the site already provides elan. Otherwise, install the official
launcher in your account without selecting a default Lean version:

```bash
curl --proto '=https' --tlsv1.2 -fLsS \
  https://elan.lean-lang.org/elan-init.sh -o "$HOME/elan-init.sh"
sh "$HOME/elan-init.sh" -y --default-toolchain none --no-modify-path
export PATH="$HOME/.elan/bin:$PATH"
elan --version
```

No root access is required. The job installs the project's pinned Lean version
and adds `${ELAN_HOME:-$HOME/.elan}/bin` to PATH.
[Official elan installation and toolchain behavior](https://github.com/leanprover/elan/blob/master/README.md).

## 3. Clone into persistent storage

The following uses home; replace it with a persistent project directory if
home has a restrictive quota. Avoid allocation-local scratch unless you arrange
checkpoint preservation yourself:

```bash
mkdir -p "$HOME/eleven-square-work"
cd "$HOME/eleven-square-work"
git clone --branch codex/simplification-verifier-20261003 \
  https://github.com/Queuingtheorydotcom/11SquaresFormalized.git Formalized
cd Formalized
git status --short
git rev-parse HEAD
cat lean-toolchain
mkdir -p .verification
df -h .
df -i .
```

Record the commit with your result. Start from an unchanged pushed checkout,
with the guide and scripts already tracked. Keep `lean-toolchain` and
`lake-manifest.json` unchanged; do not run `lake update` or switch commits during
replay.

The first run needs HTTPS access to GitHub/releases and the mathlib cache service.
For RHEL's CA certificate bundle, export this before setup or submission:

```bash
export CURL_CA_BUNDLE=/etc/pki/tls/certs/ca-bundle.crt
```

This also directs mathlib's cached curl to the system's trusted certificate file.
If compute-node networking is permitted, the batch job handles preparation.
Otherwise, prepare on a site-approved download/build node using the SAME
persistent checkout and user toolchain locations:

```bash
elan toolchain install leanprover/lean4:v4.34.1
lake exe cache get
```

These install Lean and compile/run mathlib's cache utility to install dependency
artifacts, without
starting the full packing-proof replay. Preparation can itself use substantial
RAM/time; follow site policy for login nodes. After both commands finish,
submit with `ELEVEN_SQUARE_SETUP=0`. Retain `.lake/`, `.verification/` and the
tracked source tree. On this branch, `verify.py --setup` installs dependencies
only. Do not run `materialize_wand125.py` or restore the original release layout
over these simplified sources. Use a separate persistent checkout from the
older proof branch.

## 4. Submit the full job

From the repository root on the submission host:

```bash
cd "$HOME/eleven-square-work/Formalized"
mkdir -p .verification
export ELEVEN_SQUARE_PYTHON=python3.11
export ELEVEN_SQUARE_SETUP=1
export CURL_CA_BUNDLE=/etc/pki/tls/certs/ca-bundle.crt
export ELEVEN_SQUARE_MAX_PARALLEL=96
export ELEVEN_SQUARE_JOBS=2
proof_job_id=$(sbatch --parsable --export=ALL --account YOUR_ACCOUNT --partition YOUR_PARTITION \
  --cpus-per-task=192 --mem=1300G --time=1-00:00:00 \
  scripts/run_single_node_verification.sbatch)
proof_job_id=${proof_job_id%%;*}
printf 'Job ID: %s\n' "$proof_job_id"
```

Create `.verification` BEFORE submission: Slurm opens its output path before
the script runs. Use setup `0` if the preparation in step 3 has completed.
The script defaults to 100 concurrent Lean processes, two threads per new
process and an 85-percent advisory memory target. The example above uses 96
processes for 192 allocated physical cores. For 180 allocated physical cores,
request `--cpus-per-task=180` and export `ELEVEN_SQUARE_MAX_PARALLEL=90`.
Optional overrides:

```bash
export ELEVEN_SQUARE_MAX_PARALLEL=96
export ELEVEN_SQUARE_JOBS=2
export ELEVEN_SQUARE_MEMORY_PERCENT=85
```

The Slurm defaults are one node, 200 CPUs, 1,300 GiB RAM and three days. Override
account, partition, CPU count, memory, time or node selection with `sbatch`
options according to site policy. Add `--time 1-00:00:00` if only one day is
allowed; subsequent allocations can resume. If requesting fewer CPUs, reduce
concurrency/threads accordingly.

Dependencies must be accepted before dependents launch, so actual concurrency
can fall below its ceiling. `--jobs` controls threads within a new compiler;
matching checkpoints keep their originally recorded thread count. Only one
verifier may own a checkout. Do not submit overlapping jobs against the same
directory. A later allocation may use another node if the entire checkout
and elan installation remain accessible there on persistent storage.

## 5. Watch progress

```bash
squeue -j "$proof_job_id"
tail -f ".verification/slurm-$proof_job_id.log"
```

The log appears when the job starts. Ctrl-C stops `tail`, not the job. Setup
prints dependency/cache messages and then starts compilation: `--setup` is
NOT download-only. Compilation prints status lines, for example:

```text
[12/24000] started Sqpack.Example
[12/24000] accepted Sqpack.Example
[8/24000] cached ElevenSquare.Example
```

The names/counts illustrate the format. The numerator is the module's position
in dependency order, NOT the number completed. Parallel completions arrive out
of order. Other outcomes include `failed`, `interrupted` and `blocked`.
There is no graphical progress bar, reliable percent-of-work estimate or ETA.
A large module can be silent for a long time while its compiler runs. Dependency setup
and final auditing also take time outside per-module compilation messages.

Compiler output is in `.verification/MODULE.log`, with dots retained, e.g.
`.verification/ElevenSquare.Verification.log`. Module `.json` receipts record
acceptance/fingerprints and elapsed time. Slurm accounting is available with:

```bash
sstat -j "$proof_job_id" --format=JobID,AveCPU,MaxRSS
sacct -j "$proof_job_id" --format=JobID,State,ExitCode,Elapsed,MaxRSS
```

Available accounting fields/steps depend on the site's configuration.

## 6. Resume after allocation loss or stop deliberately

Accepted modules survive interruption when their receipts, objects and logs
are preserved. Restart validates current source, compiler, configuration,
objects and transitive local dependency fingerprints before reusing acceptance.
Changed inputs trigger rechecking. Failed, interrupted or unpublished modules
run again. There is NO checkpoint inside an individual Lean module: a module
still compiling at cutoff restarts from its beginning. SIGTERM cleanup is
supported; SIGKILL cannot publish an unfinished object as a newly accepted check.

After the old job ends, from the SAME checkout:

```bash
cd "$HOME/eleven-square-work/Formalized"
# Only needed if you previously requested a drain:
rm -f .verification/STOP
export ELEVEN_SQUARE_PYTHON=python3.11
export ELEVEN_SQUARE_SETUP=0
export CURL_CA_BUNDLE=/etc/pki/tls/certs/ca-bundle.crt
export ELEVEN_SQUARE_MAX_PARALLEL=96
export ELEVEN_SQUARE_JOBS=2
proof_job_id=$(sbatch --parsable --export=ALL --account YOUR_ACCOUNT --partition YOUR_PARTITION \
  --cpus-per-task=192 --mem=1300G --time=1-00:00:00 \
  scripts/run_single_node_verification.sbatch)
proof_job_id=${proof_job_id%%;*}
printf 'Resumed job ID: %s\n' "$proof_job_id"
```

Do not use `--fresh`, delete `.verification/` or `.lake/`, run `lake clean`,
remove generated sources or reclone into an empty directory if retaining work.
The lock file can remain: its OS lock is released when the verifier process
exits. If setup was interrupted, retry with `ELEVEN_SQUARE_SETUP=1` instead.

To request a graceful stop from another shell sharing this checkout:

```bash
touch .verification/STOP
```

The job passes `--stop-file .verification/STOP`. The verifier stops launching
new modules, finishes active ones and exits nonzero without finalizing incomplete
work. This is a drain, not an immediate stop: an active huge module may still
outlast the allocation. Create STOP sufficiently early. Remove it before
resubmitting; the launcher refuses a new attempt while STOP exists.
`scancel JOB_ID` cancels immediately, preserving accepted modules but forfeiting
active module work.

## 7. Verification lifecycle and outputs

The job uses the tracked simplified sources, scans admissions/imports, installs
the pinned toolchain and mathlib cache when setup is enabled, and schedules ALL
local `ElevenSquare` and `Sqpack` modules. Lean
elaborates/type-checks them and writes `.olean` objects. It does not run a
packing-search executable or a proof program's `main`. Trusted Lean/Lake/mathlib
setup, tactics and initializers can execute during preparation and checking.

Explicit `#print axioms` queries, including public targets, are audited. With
the current empty admission inventory, only `propext`, `Classical.choice` and
`Quot.sound` are permitted. After complete replay success,
`finalize_verification.py --write` validates the full current receipt graph,
source/configuration/object hashes and axiom logs before writing evidence.
The job then requires optimality proved with zero admissions and writes a
compact completion receipt specific to its job ID.

After Slurm reports `COMPLETED` and exit `0:0`, the log should end with
`COMPLETE: optimality verified; ... local modules checked.` and a receipt path.

| File | Meaning |
| --- | --- |
| `.verification/completion-JOB_ID.json` | Small successful-job summary with audit/manifest SHA-256 hashes. |
| `.verification/result.json` | Full verifier status and axiom-query results. |
| `verification/wand125-upgrade.json` | Finalizer-validated full-source audit. |
| `verification/source-check.json` | Current source/admission check. |
| `MANIFEST.json` | Portable source/evidence file hashes. |
| `.verification/MODULE.json` and `MODULE.log` | Local checkpoints and compiler diagnostics. |
| `.lake/build/lib/lean/` | Compiled local objects for resume/revalidation. |

## 8. Programmatic completion check

Set `proof_job_id` to the completed job's ID. Check its receipt against the
finalizer audit and manifest:

```bash
python3.11 - "$proof_job_id" <<'PY'
import hashlib
import json
import sys
from pathlib import Path

receipt = json.loads(Path(f'.verification/completion-{sys.argv[1]}.json').read_text())
audit_path = Path('verification/wand125-upgrade.json')
audit = json.loads(audit_path.read_text())
checks = [
    receipt.get('status') == audit.get('status') == 'OPTIMALITY_PROVED',
    receipt.get('global_optimality_proved') is audit.get('global_optimality_proved') is True,
    receipt.get('full_upgrade_verified') is audit.get('full_upgrade_verified') is True,
    audit.get('explicit_native_admissions') == 0,
    receipt.get('checked_modules') == audit.get('checked_modules'),
    receipt.get('lean_toolchain') == audit.get('lean_toolchain'),
    receipt.get('mathlib_revision') == audit.get('mathlib_revision'),
    receipt.get('audit_sha256') == hashlib.sha256(audit_path.read_bytes()).hexdigest(),
    receipt.get('manifest_sha256') == hashlib.sha256(Path('MANIFEST.json').read_bytes()).hexdigest(),
]
if not all(checks):
    raise SystemExit('FAIL: completion receipt/audit/manifest mismatch')
print('PASS: completed verification receipt matches the full audit and manifest')
PY
```

A missing receipt or mismatch fails. This receipt is a summary, NOT an
independently checkable proof certificate. To revalidate current sources,
objects and axiom logs locally without recompiling, retain the working directory
and run:

```bash
python3.11 scripts/finalize_verification.py
```

Archive the receipt, final audit, manifest, source check and Slurm log as the
portable record. Retain objects, module receipts and logs for local revalidation.
Finalization changes three tracked evidence files; review before committing or
pushing them. The job does not push anything.

## 9. Compilation error or incomplete run

Verification/finalizer failure makes the job exit nonzero without producing its
job-specific completion receipt. `--keep-going` checks independent modules after
failures; dependents are blocked. A completed failed schedule writes
`.verification/incomplete-result.json` listing failed/blocked modules. Abrupt
termination may leave no such summary; module receipts and the Slurm log still
record progress.

Read `.verification/slurm-JOB_ID.log`, then the failed module's
`.verification/MODULE.log`. Preserve the logs, commit and toolchain version when
reporting a proof/compiler error. For `TIMEOUT` or `PREEMPTED`, obtain another
allocation and resume. For `OUT_OF_MEMORY`, reduce concurrency or increase memory.
Type-checking errors need investigation and a source fix rather than repeated
identical attempts.

Selected-module acceptance or a source-only pass cannot satisfy finalization.
For stale-input, missing-object/log or partial-coverage refusal, finish a full
`verify.py --all --keep-going` run with the intended sources and retry. An older
receipt/result does not make a later failed job successful: check the current
job's completion receipt and Slurm exit status.

The guide/launcher are checked locally using fixture tests and shell syntax
validation. No new software was installed or Slurm allocation started locally;
the complete Lean replay remains to be performed on the node.
