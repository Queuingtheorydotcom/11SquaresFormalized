# Verification execution and isolation

The current verifier is **not a security sandbox**. Python, Lake, Lean, and
their child processes run with the invoking account's permissions. `lake env`
sets build paths; Slurm allocates resources. Neither isolates untrusted code
from readable host files, writable host files, credentials, or network access.

Lean elaboration executes tactics and metaprograms. Project configuration and
dependency setup can also execute code. The verifier's source scan, empty
admission inventory, and axiom audit assess proof assembly and proof assumptions;
they do not establish that compiling the source is safe for the host. Pinned
hashes establish which inputs were used, not that those inputs are benign.

For untrusted sources, run preparation, compilation, and artifact inspection
inside an independently configured isolation boundary. Prefer a disposable VM,
or a cluster-approved container with a restricted policy:

- Expose only a dedicated disposable proof workspace and required toolchain.
- Do not expose the host home directory, credentials, SSH agent, container
  daemon sockets, or unrelated shared storage. Start with a sanitized environment.
- Prepare downloads within that boundary, without credentials. Disable network
  access for the compilation and audit phase, and omit `--setup` then.
- Run without elevated privileges, retaining resource limits and process cleanup.
- Test filesystem, environment, and network restrictions before compiling the
  proof. A container runtime's name alone is not evidence of these restrictions.

Apptainer normally binds the host home and working directory, and sites can
configure additional mounts. Those defaults must be restricted explicitly.
Containers share the host kernel; use a disposable VM when that threat matters.

The supplied Slurm example requires `ELEVEN_SQUARE_ALLOW_HOST_EXECUTION=1`
before running. This flag acknowledges the unsandboxed behavior; it does not
create or validate isolation. Do not enable it on an ordinary account for
untrusted sources. A container wrapper and its cluster validation are pending.

## Stronger proof validation

`leanchecker` replays compiled declarations through Lean's kernel. It is not a
host security sandbox, and loading untrusted `.olean` files should itself be
isolated. The current verifier does not invoke it or Comparator.

Comparator additionally checks a proposed proof against a separately trusted
statement and definitions, and can use an independent checker. Its sandbox
policy must also be reviewed for readable secrets and network access; do not
assume every sandbox hides the host filesystem. Integrating it requires a
trusted packing specification and compatible pinned checking tools.

References:

- [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
- [Comparator](https://github.com/leanprover/comparator)
- [Apptainer mounts](https://apptainer.org/docs/user/latest/bind_paths_and_mounts.html)

No full security audit of all restored certificate sources or dependencies has
been completed. The JSON success reports assume that the runner and evidence
have not been compromised; hashes alone do not establish this assumption.
