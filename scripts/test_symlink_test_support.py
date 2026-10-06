"""Fixture privilege failures must never conceal other filesystem errors."""
import unittest
from unittest import mock

from symlink_test_support import symlink_or_skip


class SymlinkPrerequisiteTests(unittest.TestCase):
    def test_windows_privilege_failure_skips_only_the_fixture(self):
        error = OSError('fixture privilege denied')
        error.winerror = 1314
        link = mock.Mock()
        link.symlink_to.side_effect = error
        with mock.patch('symlink_test_support.sys.platform', 'win32'):
            with self.assertRaisesRegex(unittest.SkipTest, 'privilege is unavailable'):
                symlink_or_skip(self, link, 'target', target_is_directory=True)
        link.symlink_to.assert_called_once_with('target', target_is_directory=True)

    def test_other_filesystem_errors_are_not_skipped(self):
        for platform, winerror in [('win32', 5), ('win32', None), ('linux', 1314)]:
            error = OSError('unexpected fixture failure')
            if winerror is not None:
                error.winerror = winerror
            link = mock.Mock()
            link.symlink_to.side_effect = error
            with self.subTest(platform=platform, winerror=winerror):
                with mock.patch('symlink_test_support.sys.platform', platform):
                    with self.assertRaises(OSError) as caught:
                        symlink_or_skip(self, link, 'target')
                self.assertIs(caught.exception, error)


if __name__ == '__main__':
    unittest.main()
