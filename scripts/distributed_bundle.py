"""Private, sanitized checkpoints for an exactly matched distributed replay.

Both public functions require the caller to hold this checkout's verifier.lock.
They never invoke Lean, acquire a second lock, or claim completion. The caller
must measure compiler_identity from the executable used by the worker. A bundle
is untrusted checkpoint material: normal verify.py and the full finalizer remain
mandatory after importing it. No upload or network operation exists here.
"""
from contextlib import contextmanager
import gzip
import hashlib
import io
from itertools import chain
import json
import os
from pathlib import Path
import re
import shutil
import stat
import tarfile
import tempfile

from check_sources import code_only, import_names
from verify_support import STANDARD_AXIOMS, audit_axioms, input_digest, lean_arguments


SCHEMA = 'eleven-square-checkpoint-v1'
MANIFEST = 'checkpoint.json'
CONTEXT = {'lean-toolchain', 'lakefile.lean', 'lake-manifest.json'}
MODULE = re.compile(r'(?:ElevenSquare|Sqpack)(?:\.[A-Za-z0-9_]+)*\Z')
DIGEST = re.compile(r'[0-9a-f]{64}\Z')
PRINTED = re.compile(
    r"^'([^']+)' (?:depends on axioms: \[([^]]*)\]|(does not depend on any axioms))", re.M)
MAX_ARCHIVE_BYTES = 512 * 1024**2
MAX_EXPANDED_BYTES = 8 * 1024**3
MAX_JSON_BYTES = 32 * 1024**2
MAX_LOG_BYTES = 64 * 1024**2
BLOCK = 1024**2
# Inspect both ordinary strings and their UTF-16 representation in opaque
# objects. This conservative screen is not a claim to recognize all personal
# information: only allowlisted structured evidence is exported alongside them.
PRIVATE = re.compile(
    rb'(?:(?<![A-Za-z0-9])[A-Za-z]:[\\/][A-Za-z_][A-Za-z0-9_. -]{2,}[\\/]|'
    rb'/(?:home|Users|Documents and Settings)/|'
    rb'\\\\[A-Za-z0-9_.-]+\\|'
    rb'(?<![A-Za-z0-9_.+%-])[A-Za-z0-9_.+%-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}|'
    rb'-----BEGIN (?:[A-Z ]+ )?PRIVATE KEY-----|'
    rb'gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|'
    rb'sk-[A-Za-z0-9_-]{20,}|AKIA[A-Z0-9]{16}|'
    rb'eyJ[A-Za-z0-9_-]{10,}\.[A-Za-z0-9_-]{10,}\.[A-Za-z0-9_-]{10,}|'
    rb'(?i:authorization\s*:\s*bearer\s+\S+|'
    rb'(?:password|access_token|refresh_token|client_secret)\s*[=:]\s*\S+))')
UTF16_ASCII = (re.compile(rb'(?:[\x01-\x7f]\x00){4,}'),
               re.compile(rb'(?:\x00[\x01-\x7f]){4,}'))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def json_bytes(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'),
                       ensure_ascii=True, allow_nan=False) + '\n').encode('ascii')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def _pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key')
        result[key] = value
    return result


def _json(data):
    require(len(data) <= MAX_JSON_BYTES, 'Checkpoint JSON exceeds bound')
    return json.loads(data, object_pairs_hook=_pairs,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('Nonfinite JSON value')))


def _module(name):
    require(isinstance(name, str) and len(name) <= 240 and MODULE.fullmatch(name),
            'Invalid checkpoint module identifier')
    return name


def triple(module):
    _module(module)
    return ('.lake/build/lib/lean/' + module.replace('.', '/') + '.olean',
            '.verification/' + module + '.json', '.verification/' + module + '.log')


def _safe_path(root, relative):
    """Refuse links/junctions in both existing files and destination parents."""
    path = Path(relative)
    require(not path.is_absolute() and '..' not in path.parts, 'Unsafe checkpoint path')
    path = root / path
    for part in (path, *path.parents):
        if part == root.parent:
            break
        try:
            info = part.lstat()
        except FileNotFoundError:
            continue
        require(not stat.S_ISLNK(info.st_mode) and not
                (getattr(info, 'st_file_attributes', 0) &
                 getattr(stat, 'FILE_ATTRIBUTE_REPARSE_POINT', 0)),
                'Linked checkpoint path is forbidden')
    return path


def _private_path(root, value):
    path = Path(value)
    if not path.is_absolute():
        path = root / path
    try:
        relative = path.relative_to(root)
    except ValueError:
        raise ValueError('Checkpoint archives must stay inside .verification') from None
    require(relative.parts and relative.parts[0] == '.verification' and len(relative.parts) > 1,
            'Checkpoint archives must stay inside .verification')
    require(path.name.endswith('.tar.gz'), 'Checkpoint archives require a .tar.gz filename')
    return _safe_path(root, relative)


class PrivacyScan:
    def __init__(self, root, *, opaque=False):
        # No environment, account, hostname, or global configuration is read.
        self.root_forms = {str(root).encode('utf-8').lower(),
                           str(root).replace('\\', '/').encode('utf-8').lower()}
        self.tail = b''
        self.opaque = opaque

    @staticmethod
    def _utf8_context(data, match):
        """Ignore a binary email coincidence only with complete contrary evidence.

        Lean's string representation is UTF-8 and includes a NUL terminator
        (lean_string_object in the pinned runtime header). An email-like byte
        sequence inside a complete invalid-UTF-8 NUL-delimited span cannot be
        such a string. Missing boundaries stay conservative, including chunks.
        """
        before = data.rfind(b'\x00', 0, match.start())
        after = data.find(b'\x00', match.end())
        if before < 0 or after < 0:
            return True
        try:
            data[before + 1:after].decode('utf-8')
            return True
        except UnicodeDecodeError:
            return False

    def feed(self, block):
        data = self.tail + block
        # NUL-stripping arbitrary object bytes can stitch unrelated binary
        # values into a fictitious path. Inspect actual contiguous UTF-16 ASCII
        # runs instead, preserving checks for either byte order and raw UTF-8.
        candidates = (match.group()[offset::2]
                      for offset, pattern in enumerate(UTF16_ASCII)
                      for match in pattern.finditer(data))
        for candidate in chain((data,), candidates):
            for match in PRIVATE.finditer(candidate):
                if (self.opaque and candidate is data and b'@' in match.group()
                        and not self._utf8_context(data, match)):
                    continue
                raise ValueError('Potential private data in checkpoint payload')
            lowered = candidate.lower()
            require(not any(form in lowered for form in self.root_forms),
                    'Private checkout path in checkpoint payload')
        self.tail = data[-4096:]


def _scan(data, root):
    PrivacyScan(root).feed(data)
    return data


def _read(path, limit=MAX_JSON_BYTES):
    require(path.is_file(), 'Missing checkpoint file')
    size = path.stat().st_size
    require(size <= limit, 'Oversized checkpoint file')
    with path.open('rb') as stream:
        # Reading the upper bound can reserve gigabytes even for a tiny file.
        data = stream.read(size + 1)
    require(len(data) == size, 'Checkpoint file changed during reading')
    return data


def _hash_file(path, root, *, scan=True):
    before = path.stat()
    require(stat.S_ISREG(before.st_mode), 'Nonregular checkpoint file')
    hasher, size, privacy = hashlib.sha256(), 0, PrivacyScan(root, opaque=True)
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(BLOCK), b''):
            if scan:
                privacy.feed(block)
            hasher.update(block)
            size += len(block)
            require(size <= MAX_EXPANDED_BYTES, 'Checkpoint file exceeds bound')
    after = path.stat()
    require((before.st_size, before.st_mtime_ns, before.st_ctime_ns) ==
            (after.st_size, after.st_mtime_ns, after.st_ctime_ns) and size == before.st_size,
            'Checkpoint file changed during validation')
    return {'sha256': hasher.hexdigest(), 'bytes': size}


def validate_plan(root, plan, compiler_identity):
    """Validate portable policy and current configuration without running tools."""
    root = Path(root).resolve()
    require(isinstance(plan, dict) and plan.get('distribution_schema') == 'eleven-square-workers-v1'
            and plan.get('schema_version') == 1, 'Unsupported distributed plan')
    _scan(json_bytes(plan), root)
    require(isinstance(compiler_identity, dict) and set(compiler_identity) ==
            {'version', 'binary_sha256', 'platform'}, 'Invalid compiler identity')
    require(compiler_identity == plan.get('compiler_identity'), 'Exact compiler identity mismatch')
    platform = compiler_identity['platform']
    require(platform in {'windows-x86_64', 'linux-x86_64'} and plan.get('platform') == platform,
            'Compiler platform mismatch')
    require(plan.get('compiler_policy') == {'required_platform': platform,
            'identity': 'exact-version-and-binary-sha256'}, 'Unsupported compiler policy')
    require(isinstance(compiler_identity['binary_sha256'], str) and
            DIGEST.fullmatch(compiler_identity['binary_sha256']), 'Invalid compiler binary hash')
    version = compiler_identity['version']
    require(isinstance(version, str), 'Invalid compiler version')
    parsed = re.fullmatch(r'Lean \(version ([A-Za-z0-9.+-]+), ([A-Za-z0-9_-]+), '
                          r'commit ([0-9a-f]{40}), (Release|Debug)\)', version)
    require(parsed is not None and parsed[2].startswith('x86_64-') and
            ('windows' in parsed[2] if platform == 'windows-x86_64' else 'linux' in parsed[2]),
            'Compiler version/platform mismatch')
    require(plan.get('lean_toolchain') == 'leanprover/lean4:v' + parsed[1],
            'Compiler/toolchain mismatch')
    context = plan.get('build_context_sha256')
    require(isinstance(context, dict) and set(context) == CONTEXT, 'Incomplete build context')
    for name, expected in context.items():
        require(isinstance(expected, str) and DIGEST.fullmatch(expected), 'Invalid configuration hash')
        require(digest(_read(_safe_path(root, name))) == expected, 'Current build configuration differs')
    require(_read(_safe_path(root, 'lean-toolchain')).decode('utf-8').strip() == plan['lean_toolchain'],
            'Current toolchain differs')
    graph, sources, sizes = plan.get('dependencies'), plan.get('source_sha256'), plan.get('source_bytes')
    require(all(isinstance(item, dict) for item in (graph, sources, sizes)) and
            set(graph) == set(sources) == set(sizes), 'Incomplete planned source graph')
    require(isinstance(plan.get('graph_sha256'), str) and DIGEST.fullmatch(plan['graph_sha256']),
            'Invalid graph digest')
    require(len({m.lower() for m in graph}) == len(graph), 'Case-colliding module identifiers')
    for module, deps in graph.items():
        _module(module)
        require(isinstance(deps, list) and all(isinstance(d, str) for d in deps)
                and deps == sorted(set(deps)) and set(deps) <= graph.keys(), 'Invalid dependency list')
        require(isinstance(sources[module], str) and DIGEST.fullmatch(sources[module]), 'Invalid source hash')
        require(type(sizes[module]) is int and sizes[module] >= 0, 'Invalid source size')
    # Iterative order avoids recursion limits on long imported certificate chains.
    remaining = {m: len(ds) for m, ds in graph.items()}
    users = {m: [] for m in graph}
    for module, deps in graph.items():
        for dep in deps:
            users[dep].append(module)
    ready, order = sorted(m for m, n in remaining.items() if not n), []
    while ready:
        module = ready.pop()
        order.append(module)
        for user in users[module]:
            remaining[user] -= 1
            if not remaining[user]:
                ready.append(user)
    require(len(order) == len(graph), 'Planned dependency cycle')
    jobs = plan.get('job_policy', {})
    require(isinstance(jobs, dict) and set(jobs) == {'default_jobs', 'module_jobs'} and
            isinstance(jobs['module_jobs'], dict) and set(jobs['module_jobs']) == set(graph),
            'Incomplete shared compiler jobs policy')
    lean_arguments('Sqpack', jobs['default_jobs'])
    for module, count in jobs['module_jobs'].items():
        lean_arguments(module, count)
    shards = plan.get('shards')
    require(type(plan.get('shard_count')) is int and isinstance(shards, list) and
            1 <= len(shards) == plan['shard_count'] <= 64, 'Invalid worker count')
    for index, shard in enumerate(shards):
        require(isinstance(shard, dict) and type(shard.get('index')) is int and shard['index'] == index,
                'Invalid worker index')
        targets = shard.get('modules')
        require(isinstance(targets, list) and all(isinstance(m, str) for m in targets) and
                targets == sorted(set(targets)) and set(targets) <= graph.keys(), 'Invalid worker targets')
    return root, order


def worker_closure(plan, worker):
    require(type(worker) is int and 0 <= worker < plan['shard_count'], 'Invalid worker index')
    closure, pending = set(), list(plan['shards'][worker]['modules'])
    while pending:
        module = pending.pop()
        if module not in closure:
            closure.add(module)
            pending.extend(plan['dependencies'][module])
    return closure


def _source(root, plan, module):
    path = _safe_path(root, module.replace('.', '/') + '.lean')
    source = _read(path, MAX_EXPANDED_BYTES)
    require(len(source) == plan['source_bytes'][module] and digest(source) == plan['source_sha256'][module],
            'Current planned source differs: ' + module)
    code = code_only(source.decode('utf-8'))
    require(not re.search(r'\b(?:axiom|admit|native_decide|sorryAx|sorry)\b', code),
            'Unapproved proof admission in checkpoint closure: ' + module)
    local = sorted({dep for dep in import_names(code)
                    if dep.startswith(('ElevenSquare', 'Sqpack'))})
    require(local == plan['dependencies'][module], 'Current local dependency graph differs: ' + module)
    return code


def canonical_log(code, raw, root):
    """Retain every audited query, including repeats; discard other diagnostics."""
    output = raw.decode('utf-8')
    axioms = audit_axioms(code, output, STANDARD_AXIOMS, set())
    lines = []
    for name, values, _ in PRINTED.findall(output):
        require(re.fullmatch(r'[\w.\']+', name), 'Invalid axiom declaration identifier')
        values = sorted({value.strip() for value in values.split(',') if value.strip()})
        lines.append("'" + name + "' " + ('depends on axioms: [' + ', '.join(values) + ']'
                     if values else 'does not depend on any axioms'))
    canonical = ('\n'.join(lines) + ('\n' if lines else '')).encode('utf-8')
    _scan(canonical, root)
    require(audit_axioms(code, canonical.decode('utf-8'), STANDARD_AXIOMS, set()) == axioms,
            'Canonical axiom evidence differs')
    return canonical, len(lines), axioms


def _receipt(module, raw, expected, object_hash):
    receipt = _json(raw)
    require(isinstance(receipt, dict) and receipt.get('module') == module and
            receipt.get('status') == 'accepted', 'Unaccepted checkpoint receipt: ' + module)
    require(receipt.get('inputs') == expected, 'Stale or incompatible checkpoint inputs: ' + module)
    require(receipt.get('object_sha256') == object_hash, 'Changed checkpoint object: ' + module)
    return {'module': module, 'status': 'accepted', 'inputs': expected, 'object_sha256': object_hash}


def _inputs(plan, module, objects, input_ids):
    dependencies = plan['dependencies'][module]
    return {'source': plan['source_sha256'][module],
            'local_dependency_objects': {dep: objects[dep] for dep in dependencies},
            'compiler': plan['compiler_identity']['version'],
            'arguments': lean_arguments(module, plan['job_policy']['module_jobs'][module]),
            'build_context': plan['build_context_sha256'],
            'local_dependency_inputs': {dep: input_ids[dep] for dep in dependencies}}


def _identity(plan):
    return {'plan_sha256': digest(json_bytes(plan)), 'graph_sha256': plan['graph_sha256'],
            'lean_toolchain': plan['lean_toolchain'], 'build_context_sha256': plan['build_context_sha256'],
            'compiler_identity': plan['compiler_identity'], 'compiler_policy': plan['compiler_policy'],
            'platform': plan['platform'], 'job_policy_sha256': digest(json_bytes(plan['job_policy']))}


class _VerifiedReader:
    def __init__(self, stream, expected, root, *, opaque=False):
        self.stream, self.expected = stream, expected
        self.hash, self.size, self.privacy = hashlib.sha256(), 0, PrivacyScan(root, opaque=opaque)

    def read(self, size=-1):
        block = self.stream.read(size)
        self.hash.update(block)
        self.size += len(block)
        self.privacy.feed(block)
        return block

    def finish(self):
        require(self.size == self.expected['bytes'] and self.hash.hexdigest() == self.expected['sha256']
                and not self.stream.read(1), 'Checkpoint payload changed during export')


@contextmanager
def _payload(value):
    if isinstance(value, bytes):
        yield io.BytesIO(value)
    else:
        with value.open('rb') as stream:
            yield stream


def _summary(manifest):
    return {'status': 'CHECKPOINT_ONLY', 'worker': manifest['worker'],
            'accepted_modules': len(manifest['modules']), 'axiom_queries': manifest['axiom_queries'],
            'graph_sha256': manifest['graph_sha256'], 'global_optimality_proved': False}


def export_bundle(root, plan, worker, output, compiler_identity):
    """Export a closed accepted subset; caller holds verifier.lock throughout."""
    root, order = validate_plan(root, plan, compiler_identity)
    output = _private_path(root, output)
    closure = worker_closure(plan, worker)
    payloads, files, objects, input_ids, modules, axioms, query_count = {}, {}, {}, {}, [], {}, 0
    for module in order:
        if module not in closure or not set(plan['dependencies'][module]) <= objects.keys():
            continue
        names = triple(module)
        paths = [_safe_path(root, name) for name in names]
        if not paths[1].is_file():
            continue
        receipt = _json(_read(paths[1]))
        if not isinstance(receipt, dict) or receipt.get('status') != 'accepted':
            continue
        require(all(path.is_file() for path in paths), 'Incomplete accepted checkpoint triple: ' + module)
        code = _source(root, plan, module)
        try:
            obj = _hash_file(paths[0], root)
        except ValueError as error:
            # Mathematical module identifiers are portable; never include the
            # suspect bytes or absolute filesystem path in the diagnostic.
            raise ValueError('Object checkpoint validation refused: ' + module) from error
        inputs = _inputs(plan, module, objects, input_ids)
        cleaned = json_bytes(_receipt(module, json_bytes(receipt), inputs, obj['sha256']))
        log, count, found = canonical_log(code, _read(paths[2], MAX_LOG_BYTES), root)
        payloads.update(zip(names, (paths[0], _scan(cleaned, root), log)))
        files[names[0]] = obj
        files.update({name: {'sha256': digest(data), 'bytes': len(data)}
                      for name, data in ((names[1], cleaned), (names[2], log))})
        objects[module], input_ids[module] = obj['sha256'], input_digest(inputs)
        modules.append(module)
        axioms.update(found)
        query_count += count
    manifest = {'schema': SCHEMA, 'status': 'CHECKPOINT_ONLY', 'worker': worker,
                **_identity(plan), 'modules': sorted(modules), 'files': files,
                'axiom_queries': query_count, 'axioms_sha256': digest(json_bytes(axioms)),
                'global_optimality_proved': False}
    payloads[MANIFEST] = _scan(json_bytes(manifest), root)
    require(sum(record['bytes'] for record in files.values()) + len(payloads[MANIFEST]) <= MAX_EXPANDED_BYTES,
            'Checkpoint expanded size exceeds bound')
    output.parent.mkdir(parents=True, exist_ok=True)
    require(shutil.disk_usage(root).free > min(MAX_ARCHIVE_BYTES, MAX_EXPANDED_BYTES) + 64 * 1024**2,
            'Insufficient disk for private checkpoint export')
    descriptor, temporary_name = tempfile.mkstemp(prefix='bundle-', suffix='.tmp', dir=output.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, 'wb') as raw:
            with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0, compresslevel=1) as compressed:
                with tarfile.open(fileobj=compressed, mode='w|', format=tarfile.PAX_FORMAT) as bundle:
                    for name in (MANIFEST, *sorted(files)):
                        value = payloads[name]
                        record = files.get(name, {'bytes': len(value), 'sha256': digest(value)}
                                           if isinstance(value, bytes) else None)
                        info = tarfile.TarInfo(name)
                        info.size, info.mode = record['bytes'], 0o600
                        info.uid = info.gid = info.mtime = 0
                        info.uname = info.gname = ''
                        with _payload(value) as stream:
                            reader = _VerifiedReader(stream, record, root, opaque=name.endswith('.olean'))
                            bundle.addfile(info, reader)
                            reader.finish()
                        require(raw.tell() <= MAX_ARCHIVE_BYTES, 'Compressed checkpoint exceeds bound')
        require(temporary.stat().st_size <= MAX_ARCHIVE_BYTES, 'Compressed checkpoint exceeds bound')
        _private_path(root, output)
        os.replace(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)
    return _summary(manifest)


def _member_ok(member):
    return (member.isreg() and not member.issparse() and member.size >= 0 and
            member.uid == member.gid == member.mtime == 0 and
            member.uname == member.gname == member.linkname == '' and member.mode == 0o600 and
            member.devmajor == member.devminor == 0 and
            all(key == 'path' and value == member.name for key, value in member.pax_headers.items()))


def _replace_file(source, target):
    """Publish a complete copy with destination ACLs, never a staging hardlink."""
    descriptor, temporary_name = tempfile.mkstemp(prefix='checkpoint-', suffix='.tmp', dir=target.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, 'wb') as dest, source.open('rb') as stream:
            shutil.copyfileobj(stream, dest, BLOCK)
        os.replace(temporary, target)
    finally:
        temporary.unlink(missing_ok=True)


def _backup_interrupted(root, records):
    """Persist every old byte before replacing any failed/interrupted triple."""
    if not records:
        return None
    parent = _safe_path(root, '.verification/distributed/import-backups')
    parent.mkdir(parents=True, exist_ok=True)
    require(shutil.disk_usage(root).free > sum(record['bytes'] for record in records.values()) + 64 * 1024**2,
            'Insufficient disk for interrupted-checkpoint backup')
    backup = Path(tempfile.mkdtemp(prefix='checkpoint-', dir=parent))
    for name, record in records.items():
        source = _safe_path(root, name)
        require(_hash_file(source, root, scan=False) == record, 'Interrupted checkpoint changed before backup')
        target = backup / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        require(_hash_file(target, root, scan=False) == record, 'Interrupted checkpoint backup differs')
    (backup / 'backup.json').write_bytes(json_bytes({'schema': 'interrupted-checkpoint-backup-v1',
                                                   'files': records}))
    return backup


def import_bundle(root, plan, archive, compiler_identity):
    """Validate the entire archive before exclusive publication; never relabel."""
    root, order = validate_plan(root, plan, compiler_identity)
    archive = _private_path(root, archive)
    require(archive.is_file() and archive.stat().st_size <= MAX_ARCHIVE_BYTES,
            'Missing or oversized checkpoint archive')
    state = _safe_path(root, '.verification')
    with tempfile.TemporaryDirectory(prefix='bundle-import-', dir=state) as directory:
        stage = Path(directory)
        with tarfile.open(archive, mode='r:gz') as bundle:
            first = bundle.next()
            require(first is not None and first.name == MANIFEST and _member_ok(first) and
                    first.size <= MAX_JSON_BYTES, 'Invalid checkpoint manifest member')
            with bundle.extractfile(first) as stream:
                manifest_bytes = stream.read(MAX_JSON_BYTES + 1)
            _scan(manifest_bytes, root)
            manifest = _json(manifest_bytes)
            require(isinstance(manifest, dict), 'Invalid checkpoint manifest')
            expected_keys = {'schema', 'status', 'worker', 'modules', 'files', 'axiom_queries',
                             'axioms_sha256', 'global_optimality_proved'} | _identity(plan).keys()
            require(set(manifest) == expected_keys and manifest.get('schema') == SCHEMA and
                    manifest.get('status') == 'CHECKPOINT_ONLY' and
                    manifest.get('global_optimality_proved') is False, 'Unsupported checkpoint manifest')
            require(all(manifest.get(key) == value for key, value in _identity(plan).items()),
                    'Checkpoint graph/configuration/compiler identity differs')
            closure = worker_closure(plan, manifest['worker'])
            modules, files = manifest['modules'], manifest['files']
            require(isinstance(modules, list) and all(isinstance(m, str) for m in modules) and
                    modules == sorted(set(modules)) and set(modules) <= closure, 'Invalid checkpoint module set')
            selected = set(modules)
            require(all(set(plan['dependencies'][m]) <= selected for m in modules),
                    'Checkpoint dependency closure is incomplete')
            names = {name for module in modules for name in triple(module)}
            require(isinstance(files, dict) and set(files) == names, 'Incomplete checkpoint triples')
            for name, record in files.items():
                require(isinstance(record, dict) and set(record) == {'bytes', 'sha256'} and
                        type(record['bytes']) is int and record['bytes'] >= 0 and
                        isinstance(record['sha256'], str) and DIGEST.fullmatch(record['sha256']),
                        'Invalid checkpoint file record')
                require(not name.endswith('.json') or record['bytes'] <= MAX_JSON_BYTES,
                        'Checkpoint receipt exceeds bound')
                require(not name.endswith('.log') or record['bytes'] <= MAX_LOG_BYTES,
                        'Checkpoint log exceeds bound')
            require(sum(record['bytes'] for record in files.values()) + first.size <= MAX_EXPANDED_BYTES,
                    'Checkpoint expanded size exceeds bound')
            require(shutil.disk_usage(root).free > sum(record['bytes'] for record in files.values()) + 64 * 1024**2,
                    'Insufficient disk for checkpoint validation')
            seen = set()
            # next() is intentional: iteration would yield the already-read manifest again.
            while (member := bundle.next()) is not None:
                name = member.name
                require(name in names and name not in seen and _member_ok(member), 'Invalid checkpoint member')
                record = files[name]
                require(member.size == record['bytes'], 'Checkpoint member size differs')
                seen.add(name)
                target = stage / name
                target.parent.mkdir(parents=True, exist_ok=True)
                with bundle.extractfile(member) as stream, target.open('xb') as dest:
                    reader = _VerifiedReader(stream, record, root, opaque=name.endswith('.olean'))
                    for block in iter(lambda: reader.read(BLOCK), b''):
                        dest.write(block)
                    reader.finish()
            require(seen == names, 'Missing checkpoint members')
        objects, input_ids, query_count, axioms = {}, {}, 0, {}
        for module in order:
            if module not in selected:
                continue
            obj_name, receipt_name, log_name = triple(module)
            code = _source(root, plan, module)
            inputs = _inputs(plan, module, objects, input_ids)
            obj_hash = files[obj_name]['sha256']
            raw_receipt = _read(stage / receipt_name)
            cleaned = _receipt(module, raw_receipt, inputs, obj_hash)
            require(raw_receipt == json_bytes(cleaned), 'Noncanonical checkpoint receipt fields')
            raw_log = _read(stage / log_name, MAX_LOG_BYTES)
            log, count, found = canonical_log(code, raw_log, root)
            require(raw_log == log, 'Noncanonical checkpoint axiom log')
            objects[module], input_ids[module] = obj_hash, input_digest(inputs)
            query_count += count
            axioms.update(found)
        require(type(manifest['axiom_queries']) is int and manifest['axiom_queries'] == query_count and
                manifest['axioms_sha256'] == digest(json_bytes(axioms)), 'Checkpoint axiom inventory differs')
        # Check every collision before publishing anything. Existing timestamps
        # and warning diagnostics stay private and need not equal sanitized bytes.
        publication, replacement_records = [], {}
        for module in order:
            if module not in selected:
                continue
            obj_name, receipt_name, log_name = triple(module)
            existing_receipt = _safe_path(root, receipt_name)
            interrupted = False
            if existing_receipt.exists():
                data = _json(_read(existing_receipt))
                interrupted = (isinstance(data, dict) and data.get('module') == module and
                               data.get('status') == 'failed_or_interrupted')
            for name in (obj_name, log_name, receipt_name):
                target = _safe_path(root, name)
                if not target.exists():
                    publication.append(name)
                    continue
                if interrupted:
                    replacement_records[name] = _hash_file(target, root, scan=False)
                    publication.append(name)
                    continue
                if name == obj_name:
                    require(_hash_file(target, root) == files[name], 'Existing checkpoint object differs: ' + module)
                elif name == receipt_name:
                    expected = _json(_read(stage / name))
                    actual = _receipt(module, _read(target), expected['inputs'], expected['object_sha256'])
                    require(actual == expected, 'Existing checkpoint receipt differs: ' + module)
                else:
                    actual, _, _ = canonical_log(_source(root, plan, module), _read(target, MAX_LOG_BYTES), root)
                    require(actual == _read(stage / name, MAX_LOG_BYTES), 'Existing checkpoint log differs: ' + module)
        # This persistent private backup is complete before the first mutation.
        # It is deliberately outside the archive member allowlist and retained
        # after success or failure for local diagnosis.
        backup = _backup_interrupted(root, replacement_records)
        changed = []
        try:
            # Receipts are last for each module and dependencies precede users.
            # Exclusive copies inherit destination ACLs on Windows; hardlinks
            # from a private staging directory would preserve restrictive ACLs.
            for name in publication:
                target = _safe_path(root, name)
                target.parent.mkdir(parents=True, exist_ok=True)
                if name in replacement_records:
                    require(_hash_file(target, root, scan=False) == replacement_records[name],
                            'Interrupted checkpoint changed before replacement')
                    changed.append((name, True))
                    _replace_file(stage / name, target)
                    continue
                with target.open('xb') as dest:
                    changed.append((name, False))
                    with (stage / name).open('rb') as source:
                        shutil.copyfileobj(source, dest, BLOCK)
        except BaseException:
            failures = []
            for name, replaced in reversed(changed):
                try:
                    target = _safe_path(root, name)
                    if replaced:
                        _replace_file(backup / name, target)
                        require(_hash_file(target, root, scan=False) == replacement_records[name],
                                'Restored checkpoint differs from backup')
                    else:
                        target.unlink(missing_ok=True)
                except BaseException:
                    failures.append(name)
            require(not failures, 'Checkpoint rollback incomplete; private import backup retained')
            raise
    return _summary(manifest)
