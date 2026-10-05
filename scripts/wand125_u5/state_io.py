"""Data-only JSON checkpoints for the optional U5 certificate generators.

Rationals are integer numerator/positive-denominator pairs. Loading reconstructs
only the dictionaries, lists, tuples and Fractions used by the generators;
checkpoint contents never select Python classes or functions. Old pickle
checkpoints are deliberately unsupported: regenerate them from the archives.
"""
import json
from fractions import Fraction


FORMAT = 'wand125-u5-state-v1'
OWNERS = {str(i) for i in range(11)}


def _list(value, length=None):
    if type(value) is not list or (length is not None and len(value) != length):
        raise ValueError('Invalid checkpoint list')
    return value


def _owners(value):
    if type(value) is not dict or not set(value) <= OWNERS:
        raise ValueError('Invalid checkpoint owner map')
    return value


def _fraction(value):
    numerator, denominator = _list(value, 2)
    if type(numerator) is not int or type(denominator) is not int or denominator <= 0:
        raise ValueError('Invalid checkpoint rational')
    return Fraction(numerator, denominator)


def _vector(value, length):
    return tuple(_fraction(x) for x in _list(value, length))


def _row(value):
    lo, hi, halves = _list(value, 3)
    return (_fraction(lo), _fraction(hi), [_vector(h, 3) for h in _list(halves)])


def _decode(payload):
    if (type(payload) is not dict or set(payload) != {'format', 'rows', 'refs', 'owned'}
            or payload['format'] != FORMAT):
        raise ValueError('Unsupported checkpoint format; regenerate old pickle checkpoints')
    rows = {int(o): [_row(r) for r in _list(rs)]
            for o, rs in _owners(payload['rows']).items()}
    refs = {}
    for o, rs in _owners(payload['refs']).items():
        if any(type(r) is not str for r in _list(rs)):
            raise ValueError('Invalid checkpoint reference')
        refs[int(o)] = rs
    owned = {int(o): [_vector(p, 2) for p in _list(ps)]
             for o, ps in _owners(payload['owned']).items()}
    if set(rows) != set(refs) or any(len(rows[o]) != len(refs[o]) for o in rows):
        raise ValueError('Checkpoint rows and references differ')
    return rows, refs, owned


def load_state(path):
    with open(path, encoding='utf-8') as stream:
        return _decode(json.load(stream))


def _rational(value):
    if type(value) not in (int, Fraction):
        raise ValueError('Checkpoint rationals must be exact')
    value = Fraction(value)
    return [value.numerator, value.denominator]


def _owner_key(owner):
    if type(owner) is not int or str(owner) not in OWNERS:
        raise ValueError('Invalid checkpoint owner')
    return str(owner)


def save_state(path, state):
    rows, refs, owned = state
    payload = {
        'format': FORMAT,
        'rows': {_owner_key(o): [[_rational(lo), _rational(hi),
                                 [[_rational(x) for x in h] for h in halves]]
                                for lo, hi, halves in rs] for o, rs in rows.items()},
        'refs': {_owner_key(o): rs for o, rs in refs.items()},
        'owned': {_owner_key(o): [[_rational(x) for x in p] for p in ps]
                  for o, ps in owned.items()},
    }
    _decode(payload)
    with open(path, 'w', encoding='utf-8') as stream:
        json.dump(payload, stream, separators=(',', ':'), ensure_ascii=True)
        stream.write('\n')
