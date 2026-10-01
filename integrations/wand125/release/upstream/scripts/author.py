"""Read files of the author's package (Queuingtheorydotcom/11SquaresOptimal f9e0de7) by path,
from a local clone with Git LFS objects (data/INDEX.json -> data/objects/xx/<sha>.gz)."""
import gzip
import hashlib
import json
import os

ROOT = os.environ['N11_AUTHOR']   # directory with the author's data/INDEX.json and data/objects/
_index = None


def index():
    global _index
    if _index is None:
        _index = json.load(open(os.path.join(ROOT, 'data/INDEX.json')))
    return _index


def sha_of(path):
    return index()['files']['evidence/' + path]


def read_bytes(path):
    h = sha_of(path)
    obj = index()['objects'][h]['object']
    raw = gzip.open(os.path.join(ROOT, obj)).read()
    assert hashlib.sha256(raw).hexdigest() == h, path
    return raw


def read_json(path):
    return json.loads(read_bytes(path))
