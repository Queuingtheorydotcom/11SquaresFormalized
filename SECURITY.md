# Verification execution and isolation

Use `python3 -I scripts/verify_container.py` for automatic isolation of untrusted
proof sources. The raw `scripts/verify.py`, its setup helpers and ordinary Lake
commands execute code with the invoking account's permissions. Lean elaboration
can run tactics, metaprograms, initializers and `#eval`; compilation is not a
safe operation merely because it does not run a program's `main`.

## Container lifecycle

The host must provide Python 3.11+, Git, and a local rootless Docker daemon with
cgroup v2 and the systemd cgroup driver. The launcher refuses rootful Docker,
remote daemons, unsupported resource enforcement, invalid budgets, and a dirty
Git checkout. It does not install Docker or fall back to host execution.

1. Build an image from an explicit allowlist: the Dockerfile, reviewed entrypoint
   and release downloader, pinned Lake manifest, and pinned release metadata.
   No whole-repository build context, home directory, credentials or host bind
   mounts are supplied. Git exports a clean committed snapshot as inert data;
   extraction happens inside the offline container and rejects links, devices,
   unsafe paths and Git internals.
2. Prepare a newly created private Docker volume with networking enabled. Only
   the image's reviewed downloader, the official elan bootstrap/toolchain and
   pinned mathlib/dependency code execute during preparation. A separate literal
   Lake configuration supplies the dependency bootstrap. Submission scripts,
   Lake configuration and Lean modules are not executed online.
3. Start a new offline container for source materialization, Lean compilation,
   axiom queries and finalization. Every container runs as UID/GID 10001 with
   dropped capabilities, no privilege escalation, Docker's built-in seccomp
   profile, a read-only image, limited temporary storage, and enforced CPU,
   memory/swap and PID budgets. A private named volume is its only persistent
   workspace. No host environment is forwarded; unexpected container environment
   keys, including automatically injected proxy settings, cause refusal.
4. Each entrypoint probes non-root execution, capabilities, seccomp, read-only
   root mount, actual cgroup budgets, daemon socket absence and host-canary
   invisibility. Offline stages require only the loopback interface. Cancellation
   removes the running container and its processes while retaining the volume.
5. Reuse a volume only offline. Daemon-owned labels bind it to the source commit
   and image ID. Existing `all` selects verification only, and existing `prepare`
   is refused, regardless of submission-writable markers. Interrupted preparation
   requires a new volume name. A private host-owned per-volume lock covers the
   whole lifecycle, preventing concurrent online/offline stages in one volume.
6. Reports remain in the volume. The `report` command streams only a fixed,
   size-limited report as data from another offline container; it does not
   extract attacker-controlled archives onto the host.

The supplied Slurm example invokes this launcher. Slurm allocates resources;
it does not isolate code. Site approval and accounting of the rootless daemon
and containers within the allocation are prerequisites. Docker is absent from
the development machine, so policy/hostile-fixture tests pass but actual runtime
isolation and the full proof replay have not yet been validated on a node.

## Trust and remaining limitations

The host launcher, allowlisted image inputs, Docker/runtime/kernel, Ubuntu base
and package repositories, official bootstrap installer and downloaded official
dependencies are trusted. The image tag is derived from the recipe, then the
actual image ID is bound to the volume. The Ubuntu tag and bootstrap installer
are evolving inputs; this is not a fully reproducible, independently authenticated
bootstrap. Pinned proof hashes identify data but do not establish its safety.

Containers share the host kernel. Use a disposable VM when protection against
kernel exploits is required. The persistent workspace has **no disk quota**;
untrusted code can exhaust the Docker storage filesystem. Use dedicated storage
or a site-enforced quota. Review/runtime probes supplement these restrictions;
they are not a complete demonstration that all host information is inaccessible.

A focused independent static review found no malicious payload in its inspected
scope. It did find `pickle.load` in optional wand125 generation helpers, which
can execute malicious cache/checkpoint contents. Those helpers are not invoked
by this verification path. The review inspected execution/build scripts and
targeted Lean keywords, not every generated proof body, downloaded dependency
or toolchain. It cannot establish absence of malicious code in the entire tree.

Code in the offline workspace can modify its tools, artifacts and reports.
Consequently a JSON success receipt is not an adversarially independent proof
certificate. The volume is never returned to an online stage after such execution.
This wrapper focuses on host containment, not mathematical correctness.

## Stronger proof validation

`leanchecker` replays compiled declarations through Lean's kernel; untrusted
objects should still be loaded inside isolation. Comparator also compares the
proof against a separately trusted statement and definitions. Neither tool is
currently invoked by the verifier, and neither name alone establishes a safe
filesystem/network policy.

References:

- [Docker rootless mode](https://docs.docker.com/engine/security/rootless/)
- [Rootless resource limitations](https://docs.docker.com/engine/security/rootless/tips/)
- [Docker run restrictions](https://docs.docker.com/reference/cli/docker/container/run/)
- [Docker offline network](https://docs.docker.com/engine/network/drivers/none/)
- [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
- [Comparator](https://github.com/leanprover/comparator)
