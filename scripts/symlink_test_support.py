"""Keep filesystem safety tests runnable without Windows symlink privileges."""
import sys


def symlink_or_skip(test, link, target, *, target_is_directory=False):
    """Skip only when Windows cannot create the fixture for a symlink test."""
    try:
        link.symlink_to(target, target_is_directory=target_is_directory)
    except OSError as error:
        if sys.platform == 'win32' and getattr(error, 'winerror', None) == 1314:
            test.skipTest('Windows symlink creation privilege is unavailable')
        raise
