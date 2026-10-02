"""Small synthetic receipts exercise transfer without invoking a compiler."""
import copy
import gzip
import io
import json
from pathlib import Path
import shutil
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import distributed_bundle as bundle
from verify_support import input_digest, lean_arguments


class BundleTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(__file__).resolve().parents[1] / '.verification'
        scratch.mkdir(exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix='test-bundle-', dir=scratch)
        self.root = Path(self.temporary.name) / 'producer'
        self.root.mkdir()
        self.addCleanup(self.temporary.cleanup)
        self.identity = {'version': 'Lean (version 4.34.1, x86_64-w64-windows-gnu, commit ' +
                         'a' * 40 + ', Release)', 'binary_sha256': 'b' * 64, 'platform': 'windows-x86_64'}
        self.sources = {
            'Sqpack.Base': 'theorem base : True := True.intro\n#print axioms base\n#print axioms base\n',
            'ElevenSquare.Leaf': 'import Sqpack.Base\ntheorem leaf : True := base\n#print axioms leaf\n',
            'ElevenSquare.Other': 'theorem other : True := True.intro\n',
        }
        for name, data in {'lean-toolchain': 'leanprover/lean4:v4.34.1\n', 'lakefile.lean': 'import Lake\n',
                           'lake-manifest.json': '{"packages": []}\n'}.items():
            (self.root / name).write_text(data, encoding='utf-8')
        for module, source in self.sources.items():
            path = self.root / (module.replace('.', '/') + '.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(source.encode())
        graph = {'Sqpack.Base': [], 'ElevenSquare.Leaf': ['Sqpack.Base'], 'ElevenSquare.Other': []}
        self.plan = {
            'distribution_schema': 'eleven-square-workers-v1', 'schema_version': 1,
            'shard_count': 2, 'graph_sha256': 'c' * 64,
            'shards': [{'index': 0, 'modules': ['ElevenSquare.Leaf'], 'estimated_source_bytes': 100},
                       {'index': 1, 'modules': ['ElevenSquare.Other'], 'estimated_source_bytes': 100}],
            'final_modules': [], 'lean_toolchain': 'leanprover/lean4:v4.34.1',
            'build_context_sha256': {name: bundle.digest((self.root / name).read_bytes()) for name in bundle.CONTEXT},
            'compiler_policy': {'required_platform': 'windows-x86_64', 'identity': 'exact-version-and-binary-sha256'},
            'platform': 'windows-x86_64', 'compiler_identity': self.identity,
            'dependencies': graph,
            'source_sha256': {m: bundle.digest(s.encode()) for m, s in self.sources.items()},
            'source_bytes': {m: len(s.encode()) for m, s in self.sources.items()},
            'job_policy': {'default_jobs': 4, 'module_jobs': {m: 4 for m in graph}},
        }
        self.objects, self.inputs = {}, {}
        for module in ('Sqpack.Base', 'ElevenSquare.Leaf', 'ElevenSquare.Other'):
            self.add_receipt(module)
        self.archive = self.root / '.verification/distributed/checkpoint.tar.gz'

    def add_receipt(self, module):
        obj_name, receipt_name, log_name = bundle.triple(module)
        obj = ('synthetic object ' + module).encode()
        inputs = {'source': self.plan['source_sha256'][module],
                  'local_dependency_objects': {d: self.objects[d] for d in self.plan['dependencies'][module]},
                  'compiler': self.identity['version'], 'arguments': lean_arguments(module, 4),
                  'build_context': self.plan['build_context_sha256'],
                  'local_dependency_inputs': {d: input_digest(self.inputs[d]) for d in self.plan['dependencies'][module]}}
        self.objects[module], self.inputs[module] = bundle.digest(obj), inputs
        receipt = {'module': module, 'status': 'accepted', 'inputs': inputs,
                   'object_sha256': bundle.digest(obj), 'checked_at_ns': 123456, 'elapsed_seconds': 2.5,
                   'unexpected_diagnostic': 'discard this metadata'}
        leaf = module.rsplit('.', 1)[-1].lower()
        log = ("'" + leaf + "' depends on axioms: [propext]\n") * (2 if module == 'Sqpack.Base' else 1)
        if module == 'ElevenSquare.Other':
            log = ''
        for name, data in ((obj_name, obj), (receipt_name, json.dumps(receipt).encode()),
                           (log_name, ('warning: ordinary diagnostics omitted\n' + log).encode())):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)

    def export(self):
        return bundle.export_bundle(self.root, self.plan, 0, self.archive, self.identity)

    def consumer(self):
        root = Path(self.temporary.name) / 'consumer'
        root.mkdir()
        for name in bundle.CONTEXT:
            shutil.copyfile(self.root / name, root / name)
        for module in self.sources:
            name = module.replace('.', '/') + '.lean'
            (root / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(self.root / name, root / name)
        target = root / '.verification/distributed/input.tar.gz'
        target.parent.mkdir(parents=True)
        shutil.copyfile(self.archive, target)
        return root, target

    def members(self):
        with tarfile.open(self.archive, 'r:gz') as archive:
            return [(member, archive.extractfile(member).read()) for member in archive]

    def rewrite(self, transform):
        entries = self.members()
        transform(entries)
        with self.archive.open('wb') as raw, gzip.GzipFile(filename='', fileobj=raw, mode='wb', mtime=0) as zipped:
            with tarfile.open(fileobj=zipped, mode='w', format=tarfile.PAX_FORMAT) as archive:
                for info, data in entries:
                    info.size = len(data)
                    archive.addfile(info, io.BytesIO(data))

    def test_roundtrip_sanitizes_preserves_all_queries_and_is_deterministic(self):
        summary = self.export()
        original = self.archive.read_bytes()
        self.export()
        self.assertEqual(original, self.archive.read_bytes())
        self.assertEqual(summary['accepted_modules'], 2)
        self.assertEqual(summary['axiom_queries'], 3)
        self.assertIs(summary['global_optimality_proved'], False)
        for info, data in self.members():
            self.assertEqual((info.uid, info.gid, info.mtime, info.uname, info.gname), (0, 0, 0, '', ''))
            if info.name.endswith('.json') and info.name != bundle.MANIFEST:
                self.assertEqual(set(json.loads(data)), {'module', 'status', 'inputs', 'object_sha256'})
            self.assertNotIn(b'unexpected_diagnostic', data)
            self.assertNotIn(b'ordinary diagnostics', data)
        root, archive = self.consumer()
        self.assertEqual(summary, bundle.import_bundle(root, self.plan, archive, self.identity))
        for module in ('Sqpack.Base', 'ElevenSquare.Leaf'):
            object_name = bundle.triple(module)[0]
            self.assertEqual((self.root / object_name).read_bytes(), (root / object_name).read_bytes())
        self.assertEqual(summary, bundle.import_bundle(root, self.plan, archive, self.identity))

    def test_existing_raw_receipts_and_logs_are_preserved(self):
        self.export()
        names = bundle.triple('Sqpack.Base')
        before = [(self.root / name).read_bytes() for name in names]
        bundle.import_bundle(self.root, self.plan, self.archive, self.identity)
        self.assertEqual(before, [(self.root / name).read_bytes() for name in names])

    def test_partial_export_is_dependency_closed(self):
        receipt = self.root / bundle.triple('Sqpack.Base')[1]
        data = json.loads(receipt.read_bytes())
        data['status'] = 'failed_or_interrupted'
        receipt.write_text(json.dumps(data), encoding='utf-8')
        self.assertEqual(self.export()['accepted_modules'], 0)

    def test_wrong_compiler_platform_binary_or_jobs_is_rejected(self):
        for key, replacement in [('platform', 'linux-x86_64'), ('binary_sha256', 'd' * 64),
                                 ('version', self.identity['version'].replace('Release', 'Debug'))]:
            identity = dict(self.identity, **{key: replacement})
            with self.subTest(key=key), self.assertRaises(ValueError):
                bundle.export_bundle(self.root, self.plan, 0, self.archive, identity)
        plan = copy.deepcopy(self.plan)
        plan['job_policy']['module_jobs']['ElevenSquare.Leaf'] = 2
        with self.assertRaisesRegex(ValueError, 'inputs'):
            bundle.export_bundle(self.root, plan, 0, self.archive, self.identity)

    def test_incomplete_job_policy_and_changed_source_or_config_are_rejected(self):
        plan = copy.deepcopy(self.plan)
        del plan['job_policy']['module_jobs']['ElevenSquare.Other']
        with self.assertRaises(ValueError):
            bundle.export_bundle(self.root, plan, 0, self.archive, self.identity)
        source = self.root / 'Sqpack/Base.lean'
        source.write_bytes(source.read_bytes() + b'\n')
        with self.assertRaisesRegex(ValueError, 'source'):
            self.export()
        source.write_bytes(self.sources['Sqpack.Base'].encode())
        (self.root / 'lakefile.lean').write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'configuration'):
            self.export()

    def test_forged_transitive_fingerprint_is_rejected(self):
        path = self.root / bundle.triple('ElevenSquare.Leaf')[1]
        receipt = json.loads(path.read_bytes())
        receipt['inputs']['local_dependency_inputs']['Sqpack.Base'] = '0' * 64
        path.write_text(json.dumps(receipt), encoding='utf-8')
        with self.assertRaisesRegex(ValueError, 'inputs'):
            self.export()

    def test_current_import_graph_must_match_plan_even_when_source_hash_is_updated(self):
        module = 'ElevenSquare.Leaf'
        source = 'import ElevenSquare.Other\ntheorem leaf : True := True.intro\n#print axioms leaf\n'
        (self.root / 'ElevenSquare/Leaf.lean').write_bytes(source.encode())
        self.plan['source_sha256'][module] = bundle.digest(source.encode())
        self.plan['source_bytes'][module] = len(source.encode())
        with self.assertRaisesRegex(ValueError, 'dependency graph'):
            self.export()

    def test_admitted_source_refused_even_with_matching_plan_hash(self):
        module = 'Sqpack.Base'
        source = 'theorem base : True := by sorry\n#print axioms base\n#print axioms base\n'
        (self.root / 'Sqpack/Base.lean').write_bytes(source.encode())
        self.plan['source_sha256'][module] = bundle.digest(source.encode())
        self.plan['source_bytes'][module] = len(source.encode())
        with self.assertRaisesRegex(ValueError, 'admission'):
            self.export()

    def test_every_axiom_query_is_required_and_unsupported_axioms_rejected(self):
        path = self.root / bundle.triple('Sqpack.Base')[2]
        for data in [b"'base' depends on axioms: [propext]\n",
                     b"'base' depends on axioms: [sorryAx]\n" * 2,
                     b"'base' depends on axioms: [custom]\n" * 2]:
            with self.subTest(data=data):
                path.write_bytes(data)
                with self.assertRaises(ValueError):
                    self.export()

    def test_private_payload_rejected_but_public_url_is_allowed(self):
        for value in [b'C:\\Users\\example\\secret', b'/home/example/private',
                      b'example@example.invalid', b'ghp_' + b'a' * 30,
                      'C:\\Users\\example\\secret'.encode('utf-16-le')]:
            with self.subTest(kind=value[:3]), self.assertRaisesRegex(ValueError, 'private'):
                bundle._scan(value, self.root)
        bundle._scan(b'https://github.com/leanprover/lean4', self.root)
        scanner = bundle.PrivacyScan(self.root)
        scanner.feed(b'example@exam')
        with self.assertRaises(ValueError):
            scanner.feed(b'ple.invalid')

    def test_binary_nuls_do_not_stitch_fake_paths_but_real_utf16_is_checked(self):
        # This is neither a raw UNC path nor a UTF-16 string: adjacent printable
        # byte spacing is irregular. Removing all NULs fabricates a false path.
        binary = b'\x02\\\x00\x00\\abc\x00\x00\\\x01'
        bundle._scan(binary, self.root)
        values = ['\\\\example\\share\\file', 'C:\\Users\\example\\private',
                  '/home/example/private', 'example@example.invalid', 'ghp_' + 'a' * 30]
        for encoding in ('utf-16-le', 'utf-16-be'):
            for value in values:
                data = value.encode(encoding)
                with self.subTest(encoding=encoding, category=value[:1]), self.assertRaises(ValueError):
                    bundle._scan(b'\x03' + data + b'\x02', self.root)
            data = values[0].encode(encoding)
            scanner = bundle.PrivacyScan(self.root)
            scanner.feed(data[:5])
            with self.assertRaises(ValueError):
                scanner.feed(data[5:])

    def test_opaque_email_requires_string_context_without_weakening_text_checks(self):
        # The trailing UTF-8 lead is truncated by NUL, proving this is a binary
        # span rather than the runtime's NUL-terminated UTF-8 string layout.
        binary = b'\x00a@b.cd\xc3\x00'
        bundle.PrivacyScan(self.root, opaque=True).feed(binary)
        with self.assertRaises(ValueError):
            bundle._scan(binary, self.root)
        for data in (b'\x00a@b.cd\x00', b'a@b.cd', b'\x00a@b.cd', b'a@b.cd\x00',
                     '\x00text a@b.cd λ\x00'.encode('utf-8'),
                     'a@b.cd'.encode('utf-16-le'), 'a@b.cd'.encode('utf-16-be')):
            with self.subTest(length=len(data)), self.assertRaises(ValueError):
                bundle.PrivacyScan(self.root, opaque=True).feed(data)
        scanner = bundle.PrivacyScan(self.root, opaque=True)
        scanner.feed(b'\x00a@')
        with self.assertRaises(ValueError):
            scanner.feed(b'b.cd\x00')
        # Skipping one demonstrably binary coincidence must not hide a later
        # genuine string in the same object block.
        with self.assertRaises(ValueError):
            bundle.PrivacyScan(self.root, opaque=True).feed(binary + b'\x00a@b.cd\x00')

    def test_private_object_refused_even_when_hash_matches(self):
        names = bundle.triple('Sqpack.Base')
        (self.root / names[0]).write_bytes(b'/home/example/private')
        receipt = json.loads((self.root / names[1]).read_bytes())
        receipt['object_sha256'] = bundle.digest((self.root / names[0]).read_bytes())
        (self.root / names[1]).write_text(json.dumps(receipt), encoding='utf-8')
        with self.assertRaisesRegex(ValueError, 'Object checkpoint validation refused: Sqpack.Base'):
            self.export()

    def test_changed_import_identity_graph_or_policy_rejected_before_write(self):
        self.export()
        root, archive = self.consumer()
        for field in ('graph_sha256', 'source_sha256', 'job_policy'):
            plan = copy.deepcopy(self.plan)
            if field == 'graph_sha256':
                plan[field] = 'd' * 64
            elif field == 'source_sha256':
                plan[field]['ElevenSquare.Other'] = 'e' * 64
            else:
                plan[field]['default_jobs'] = 1
            with self.subTest(field=field), self.assertRaises(ValueError):
                bundle.import_bundle(root, plan, archive, self.identity)
        self.assertFalse((root / '.lake').exists())

    def test_archive_hash_or_unexpected_path_rejected_before_write(self):
        for mutation in ('bytes', 'path', 'owner', 'duplicate', 'symlink', 'pax'):
            with self.subTest(mutation=mutation):
                self.export()
                def transform(entries):
                    info, data = entries[1]
                    if mutation == 'bytes':
                        entries[1] = (info, bytes([data[0] ^ 1]) + data[1:])
                    elif mutation == 'path':
                        info.name = '../outside'
                    elif mutation == 'owner':
                        info.uname = 'untrusted-owner'
                    elif mutation == 'duplicate':
                        entries.append((copy.copy(info), data))
                    elif mutation == 'pax':
                        info.pax_headers = {'comment': 'unapproved metadata'}
                    else:
                        info.type, info.linkname = tarfile.SYMTYPE, 'outside'
                self.rewrite(transform)
                with self.assertRaises(ValueError):
                    bundle.import_bundle(self.root, self.plan, self.archive, self.identity)

    def test_rehashed_incomplete_closure_or_noncanonical_log_is_rejected(self):
        for mutation in ('closure', 'log', 'receipt'):
            with self.subTest(mutation=mutation):
                self.export()
                def transform(entries):
                    manifest = json.loads(entries[0][1])
                    if mutation == 'closure':
                        manifest['modules'].remove('Sqpack.Base')
                        dropped = set(bundle.triple('Sqpack.Base'))
                        entries[:] = [(info, data) for info, data in entries if info.name not in dropped]
                        for name in dropped:
                            del manifest['files'][name]
                    else:
                        name = bundle.triple('Sqpack.Base')[2 if mutation == 'log' else 1]
                        for index, (info, data) in enumerate(entries):
                            if info.name != name:
                                continue
                            if mutation == 'log':
                                data += b'warning: diagnostics must not be exported\n'
                            else:
                                receipt = json.loads(data)
                                receipt['unapproved_extra_field'] = 'discarded only on export'
                                data = bundle.json_bytes(receipt)
                            entries[index] = info, data
                            manifest['files'][name] = {'sha256': bundle.digest(data), 'bytes': len(data)}
                    entries[0] = entries[0][0], bundle.json_bytes(manifest)
                self.rewrite(transform)
                with self.assertRaises(ValueError):
                    bundle.import_bundle(self.root, self.plan, self.archive, self.identity)

    def test_conflict_checked_before_publishing_any_file(self):
        self.export()
        root, archive = self.consumer()
        name = bundle.triple('ElevenSquare.Leaf')[0]
        path = root / name
        path.parent.mkdir(parents=True)
        path.write_bytes(b'conflict')
        with self.assertRaisesRegex(ValueError, 'differs'):
            bundle.import_bundle(root, self.plan, archive, self.identity)
        self.assertFalse((root / bundle.triple('Sqpack.Base')[0]).exists())
        self.assertEqual(path.read_bytes(), b'conflict')

    def test_failed_publication_rolls_back_only_new_files(self):
        self.export()
        root, archive = self.consumer()
        real_copy, calls = shutil.copyfileobj, []
        def fail_second(source, destination, length):
            calls.append(1)
            if len(calls) == 2:
                destination.write(b'partial')
                raise OSError('simulated copy interruption')
            return real_copy(source, destination, length)
        with patch.object(bundle.shutil, 'copyfileobj', side_effect=fail_second):
            with self.assertRaises(OSError):
                bundle.import_bundle(root, self.plan, archive, self.identity)
        self.assertFalse(any((root / name).exists() for module in ('Sqpack.Base', 'ElevenSquare.Leaf')
                             for name in bundle.triple(module)))
        self.assertTrue(archive.is_file())

    def interrupted(self, root):
        names = bundle.triple('Sqpack.Base')
        contents = {names[0]: b'old interrupted object',
                    names[1]: bundle.json_bytes({'module': 'Sqpack.Base', 'status': 'failed_or_interrupted',
                                                'inputs': {'obsolete': True}}),
                    names[2]: b'old private diagnostics /home/example/notes\n'}
        for name, data in contents.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        return contents

    def assert_backup(self, root, contents):
        backups = list((root / '.verification/distributed/import-backups').glob('checkpoint-*'))
        self.assertEqual(len(backups), 1)
        for name, data in contents.items():
            self.assertEqual((backups[0] / name).read_bytes(), data)
        manifest = json.loads((backups[0] / 'backup.json').read_bytes())
        self.assertEqual(set(manifest['files']), set(contents))

    def test_interrupted_triple_is_backed_up_before_validated_replacement(self):
        self.export()
        root, archive = self.consumer()
        old = self.interrupted(root)
        summary = bundle.import_bundle(root, self.plan, archive, self.identity)
        self.assertEqual(summary['accepted_modules'], 2)
        self.assert_backup(root, old)
        receipt = json.loads((root / bundle.triple('Sqpack.Base')[1]).read_bytes())
        self.assertEqual(receipt['status'], 'accepted')
        # Private diagnostics preserved in backup never enter the export set.
        exported = root / '.verification/distributed/export.tar.gz'
        bundle.export_bundle(root, self.plan, 0, exported, self.identity)

    def test_replacement_failure_restores_entire_transaction_and_retains_backup(self):
        self.export()
        root, archive = self.consumer()
        old = self.interrupted(root)
        real_copy, calls = shutil.copyfileobj, []
        def fail_fourth(source, destination, length):
            calls.append(1)
            if len(calls) == 4:
                destination.write(b'partial')
                raise OSError('simulated later module interruption')
            return real_copy(source, destination, length)
        with patch.object(bundle.shutil, 'copyfileobj', side_effect=fail_fourth):
            with self.assertRaises(OSError):
                bundle.import_bundle(root, self.plan, archive, self.identity)
        for name, data in old.items():
            self.assertEqual((root / name).read_bytes(), data)
        self.assertFalse(any((root / name).exists() for name in bundle.triple('ElevenSquare.Leaf')))
        self.assert_backup(root, old)

    def test_accepted_conflict_blocks_interrupted_replacement_before_backup(self):
        self.export()
        root, archive = self.consumer()
        old = self.interrupted(root)
        for name in bundle.triple('ElevenSquare.Leaf'):
            target = root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(self.root / name, target)
        target = root / bundle.triple('ElevenSquare.Leaf')[0]
        target.write_bytes(b'accepted conflict')
        with self.assertRaisesRegex(ValueError, 'differs'):
            bundle.import_bundle(root, self.plan, archive, self.identity)
        for name, data in old.items():
            self.assertEqual((root / name).read_bytes(), data)
        self.assertFalse((root / '.verification/distributed/import-backups').exists())

    def test_small_file_reads_do_not_allocate_the_upper_bound(self):
        path = self.root / 'small'
        path.write_bytes(b'small')
        with patch.object(Path, 'open', return_value=io.BytesIO(b'small')) as opened:
            # The actual read size is asserted, independently of available RAM.
            stream = opened.return_value
            with patch.object(stream, 'read', wraps=stream.read) as read:
                self.assertEqual(bundle._read(path, bundle.MAX_EXPANDED_BYTES), b'small')
                read.assert_called_once_with(6)

    def test_compressed_limit_retains_previous_archive_and_outputs_stay_private(self):
        self.export()
        old = self.archive.read_bytes()
        with patch.object(bundle, 'MAX_ARCHIVE_BYTES', 100):
            with self.assertRaises(ValueError):
                self.export()
        self.assertEqual(self.archive.read_bytes(), old)
        with self.assertRaises(ValueError):
            bundle.export_bundle(self.root, self.plan, 0, self.root / 'tracked.tar.gz', self.identity)

    def test_symlink_parent_refused_when_platform_supports_symlinks(self):
        self.export()
        root, archive = self.consumer()
        target = root / '.lake'
        outside = root / 'linked-target'
        outside.mkdir()
        try:
            target.symlink_to(outside, target_is_directory=True)
        except OSError as error:
            if getattr(error, 'winerror', None) == 1314:
                self.skipTest('Windows symlink privilege unavailable')
            raise
        with self.assertRaisesRegex(ValueError, 'Linked'):
            bundle.import_bundle(root, self.plan, archive, self.identity)


if __name__ == '__main__':
    unittest.main()
