#!/usr/bin/env python3
"""Offline checkpoint safety tests; never invoke the compiler or hosted setup."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest import mock

import ci_replay as ci


class Checkpoints(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        (self.root / '.verification').mkdir()

    def accepted(self, module='Sqpack.A', body=b'object', **kwargs):
        names = ci.triple(module)
        values = [body, json.dumps({'status':'accepted', 'inputs':{'source':'abc'},
                  'object_sha256':hashlib.sha256(body).hexdigest(), **kwargs}).encode(), b'checked\n']
        for name, value in zip(names, values):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(value)
        return names

    def destination(self):
        dest = self.root / 'destination'
        (dest / '.verification').mkdir(parents=True)
        return dest

    def test_round_trip_and_leaf_exclusion_from_join_cache(self):
        names = self.accepted()
        archive = self.root / 'shard-00.tar.gz'
        self.assertTrue(ci.pack(self.root, archive))
        dest = self.destination()
        ci.merge(dest, [archive])
        self.assertEqual((dest / names[0]).read_bytes(), b'object')
        out = dest / 'join.tar.gz'
        ci.pack(dest, out, join=True)
        with tarfile.open(out) as bundle:
            self.assertEqual(bundle.getnames(), [])

    def test_prior_join_progress_is_retained_in_join_checkpoint(self):
        self.accepted()
        archive = self.root / 'shard-16.tar.gz'
        ci.pack(self.root, archive)
        dest = self.destination()
        ci.merge(dest, [archive])
        output = dest / 'next-join.tar.gz'
        ci.pack(dest, output, join=True)
        with tarfile.open(output) as bundle:
            self.assertEqual(len(bundle.getnames()), 3)

    def test_incomplete_triples_are_rejected(self):
        archive = self.root / 'partial.tar.gz'
        with tarfile.open(archive, 'w:gz') as bundle:
            member = tarfile.TarInfo(ci.triple('Sqpack.A')[0])
            member.size = 1
            bundle.addfile(member, io.BytesIO(b'x'))
        with self.assertRaisesRegex(ValueError, 'has no receipt'):
            ci.merge(self.destination(), [archive])

    def test_accepted_hash_tampering_is_rejected(self):
        names = self.accepted()
        (self.root / names[0]).write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'object hash differs'):
            ci.pack(self.root, self.root / 'out.tar.gz')

    def test_failed_receipts_are_excluded(self):
        self.accepted(status='failed_or_interrupted')
        archive = self.root / 'out.tar.gz'
        ci.pack(self.root, archive)
        with tarfile.open(archive) as bundle:
            self.assertEqual(bundle.getnames(), [])

    def test_oversize_is_not_exported(self):
        self.accepted()
        output = self.root / 'out.tar.gz'
        with self.assertRaisesRegex(ValueError, 'Compressed checkpoint exceeds'):
            ci.pack(self.root, output, limit=1)
        self.assertFalse(output.exists())

    def test_compressible_objects_use_compressed_budget(self):
        self.accepted(body=b'x' * (128 * 1024))
        output = self.root / 'compressed.tar.gz'
        self.assertTrue(ci.pack(self.root, output, limit=16 * 1024))
        self.assertLess(output.stat().st_size, 16 * 1024)
        ci.merge(self.destination(), [output])

    def test_expanded_size_limit_is_checked(self):
        self.accepted(body=b'x' * 1000)
        output = self.root / 'expanded.tar.gz'
        ci.pack(self.root, output)
        with mock.patch.object(ci, 'EXPANDED_LIMIT', 10):
            with self.assertRaisesRegex(ValueError, 'declared size'):
                ci.merge(self.destination(), [output])

    def test_conflicting_duplicate_objects_are_dropped_for_rebuild(self):
        self.accepted()
        first = self.root / 'shard-00.tar.gz'; ci.pack(self.root, first)
        self.accepted(body=b'different')
        second = self.root / 'shard-01.tar.gz'; ci.pack(self.root, second)
        dest = self.destination()
        self.assertEqual(ci.merge(dest, [first, second]), {'Sqpack.A'})
        self.assertFalse((dest / '.lake').exists())

    def test_identical_objects_and_inputs_allow_different_receipt_times(self):
        self.accepted(checked_at_ns=1)
        first = self.root / 'shard-00.tar.gz'; ci.pack(self.root, first)
        self.accepted(checked_at_ns=2)
        second = self.root / 'shard-01.tar.gz'; ci.pack(self.root, second)
        ci.merge(self.destination(), [first, second])

    def test_unsafe_archive_and_symlink_are_rejected(self):
        for name, kind in [('../escape', tarfile.REGTYPE), ('.verification/Sqpack.A.log', tarfile.SYMTYPE)]:
            archive = self.root / 'bad.tar.gz'
            with tarfile.open(archive, 'w:gz') as bundle:
                member = tarfile.TarInfo(name); member.type = kind
                bundle.addfile(member, io.BytesIO(b''))
            with self.assertRaisesRegex(ValueError, 'Invalid checkpoint member'):
                ci.merge(self.root, [archive])

    def test_setup_refuses_user_filesystem(self):
        with mock.patch.dict(ci.os.environ, {}, clear=True), mock.patch.object(ci.subprocess, 'run') as run:
            with self.assertRaisesRegex(ValueError, 'disposable GitHub-hosted'):
                ci.prepare()
            run.assert_not_called()


if __name__ == '__main__':
    unittest.main()
