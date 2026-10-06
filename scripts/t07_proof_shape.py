"""Recognize one known generated T07 tactic failure, not arbitrary Lean proofs."""
import re


STAGE = re.compile(r'ElevenSquare/Tasks/T07/Ext/Gen/[^/]+/S[0-9]+\.lean')

# Keep the complete adjacent declarations together: another namespace, binding,
# or proof body is outside this check. The first (length) side condition is not
# the failing bound and must not be mistaken for it.
ROW_BLOCK_PROOF = re.compile(r'''
    ^theorem\s+nrows\s*:\s*\(prev\.rows\s+(?P<rows_owner>[0-9]+)\)\.length
    \s*=\s*(?P<rows>[0-9]+)\s*:=\s*by\s+decide(?:\s+\+kernel)?\s+
    theorem\s+step_ok\s*:\s*stepB\s+prev\s+(?P<step_owner>[0-9]+)
    \s+rs\s+pcov\s+certs\s*=\s*true\s*:=\s*by\s+
    apply\s+stepB_of_row_blocks\s+
    \(width\s*:=\s*(?P<width>[0-9]+)\)\s+
    \(blocks\s*:=\s*(?P<blocks>[0-9]+)\)\s+
    \(by\s+decide\)\s+
    \(by\s+rw\s*\[nrows\]\s*;\s*rfl\)\s+
    \(by\s+rw\s*\[nrows\]\s*(?P<unsafe>;\s*decide)\)\s+
    intro\s+b\s+hb\s+
    interval_cases\s+b\s*<;>\s*(?:native_decide|decide\s+\+kernel)
    \s*(?=\Z|^(?:theorem|lemma|def|abbrev|end)\b)
''', re.MULTILINE | re.VERBOSE)


def check_row_block_proof(relpath, code):
    """Reject the confirmed full-block error in already masked Lean source.

    The caller removes comments and strings while preserving offsets. Unknown
    proof shapes are deliberately ignored; successful recognition is not a
    general proof-validity check.
    """
    if not STAGE.fullmatch(relpath):
        return
    for match in ROW_BLOCK_PROOF.finditer(code):
        if (int(match['rows_owner']) != int(match['step_owner'])
                or int(match['rows']) != int(match['width']) * int(match['blocks'])):
            continue
        line = code.count('\n', 0, match.start('unsafe')) + 1
        raise ValueError(
            f'{relpath}:{line}: generated step_ok has a full row-block cover; '
            'rw [nrows] closes the bound, so the following unconditional decide '
            'causes "No goals to be solved". Use (by rw [nrows] <;> decide).')
