#!/bin/sh
# Overlay the n = 11 Lean files onto Evan Daniel's pinned Lean project, regenerate the data from
# the author's pinned files, build, and check the axioms.
# Usage: sh build.sh <new work directory>
#   N11_JOBS=k     parallel tree checks (default 4)
#   N11_NO_BUILD=1 stop after regenerating and checking the data (no Lean build)
set -eu
UPSTREAM_URL=https://github.com/evand/square-packing.git
UPSTREAM_COMMIT=6e1223cf7ef2be4c70baaa36c0e7e7197076735a
SQPACK_SHA256=094c02f94b50aa123a2be8b61cf1655189f148b7f8f1ef2d6364dcf64b10ab6a
# The author's proof: Queuingtheorydotcom/11SquaresOptimal, commit f9e0de7 (Git LFS objects,
# addressed by the SHA256 of their content, see the author's data/INDEX.json).
AUTHOR_MEDIA=https://media.githubusercontent.com/media/Queuingtheorydotcom/11SquaresOptimal/f9e0de713a0949d1bc6a0fa6b59d96edf6c3d65c/data/objects
COVER_SHA256=df7938d9ba27095a38fabe45f8b26b259a2cc896c2ae4aac6bae874f417adc4e
PACKET_SHA256=4aca103f9d71dad6792f19c0cdd13c84f96bb1e4d7154bf843d7ea62ae009d17
JOBS=${N11_JOBS:-4}
AUTHOR_RAW=https://raw.githubusercontent.com/Queuingtheorydotcom/11SquaresOptimal/f9e0de713a0949d1bc6a0fa6b59d96edf6c3d65c
INDEX_SHA256=29d77766160f3f879d240eaf3fef0b488ec2f21e69f7bad1260b31063ecdf096
# LFS objects used by the field certificates 3, 6, 19: the replay manifest, the centre cover, three packets
AUTHOR_OBJECTS="53ef66cc8c1ee5e937fcd645a7bb831d96a65487b422d52cf67fb7d3c9b4ce61
df7938d9ba27095a38fabe45f8b26b259a2cc896c2ae4aac6bae874f417adc4e
3492cd05d8c2fd1a2aadd84c93a09c4a509171e830b7b42c5a2f049f4f11e0d3
2ee184f832a24833c348d322c4ee8741f361f3f97d4b8b0faf54974d93e981b9
8ac3b7c4093a06354850e4d804f250196ff0505bfc411ac05f4f78cbacec5734"
FIELD_CERTS="3 6 19"

HERE=$(cd "$(dirname "$0")" && pwd)
WORK=${1:?usage: sh build.sh <new work directory>}
[ ! -e "$WORK" ] || { echo "refusing existing path: $WORK" >&2; exit 2; }
if command -v sha256sum >/dev/null; then sha() { sha256sum "$1" | cut -d' ' -f1; }; else sha() { shasum -a 256 "$1" | cut -d' ' -f1; }; fi
mkdir -p "$WORK"
WORK=$(cd "$WORK" && pwd)

# 1. upstream Lean project (definitions `Packs`, `minSide`, `sq`, `ptOk`, …), unmodified
git clone -q "$UPSTREAM_URL" "$WORK/upstream"
git -C "$WORK/upstream" checkout -q "$UPSTREAM_COMMIT"
[ "$(git -C "$WORK/upstream" rev-parse HEAD)" = "$UPSTREAM_COMMIT" ]
P="$WORK/upstream/s12/lean"
[ "$(sha "$P/Sqpack.lean")" = "$SQPACK_SHA256" ] || { echo "upstream Sqpack.lean differs" >&2; exit 1; }
[ ! -e "$P/Sqpack/S11Opt" ] || { echo "upstream already has Sqpack/S11Opt" >&2; exit 1; }
mkdir -p "$P/Sqpack/S11Opt/F00" "$P/Sqpack/S11Opt/Split"
cp "$HERE"/lean/Sqpack/S11Opt/*.lean "$P/Sqpack/S11Opt/"
cp "$HERE"/lean/Sqpack/S11Opt/Split/*.lean "$P/Sqpack/S11Opt/Split/"

# 2. the author's two input files, checked by content hash
D="$WORK/data"
mkdir -p "$D/cover" "$D/field-00/research/phase3/work/continuation"
curl -sSfL "$AUTHOR_MEDIA/df/$COVER_SHA256.gz" | gunzip -c > "$D/cover/center-cover-symmetric-exact.json"
curl -sSfL "$AUTHOR_MEDIA/4a/$PACKET_SHA256.gz" | gunzip -c \
  > "$D/field-00/research/phase3/work/continuation/mask2045-omit14-packet.json"
[ "$(sha "$D/cover/center-cover-symmetric-exact.json")" = "$COVER_SHA256" ]
[ "$(sha "$D/field-00/research/phase3/work/continuation/mask2045-omit14-packet.json")" = "$PACKET_SHA256" ]

# 3. regenerate the data (exact; deterministic) and compare with the manifest
(cd "$HERE/scripts" && python3 gen.py "$P/Sqpack/S11Opt/Data.lean")
(cd "$HERE/scripts" && N11_DATA="$D" python3 field_tree.py "$P/Sqpack/S11Opt/F00")
(cd "$HERE/scripts" && N11_DATA="$D" python3 gen_final.py "$P/Sqpack/S11Opt/F00")
# the author's data index and the LFS objects of the other field certificates
A="$WORK/author"
mkdir -p "$A/data"
curl -sSfL "$AUTHOR_RAW/data/INDEX.json" > "$A/data/INDEX.json"
[ "$(sha "$A/data/INDEX.json")" = "$INDEX_SHA256" ]
for h in $AUTHOR_OBJECTS; do
  d=$(printf %s "$h" | cut -c1-2); mkdir -p "$A/data/objects/$d"
  curl -sSfL "$AUTHOR_MEDIA/$d/$h.gz" > "$A/data/objects/$d/$h.gz"
done
(cd "$HERE/scripts" && export N11_AUTHOR="$A" N11_CACHE="$WORK/cache" N11_PROCS="$JOBS" &&
  python3 field_all.py search $FIELD_CERTS && python3 field_all.py own &&
  python3 field_all.py emit "$P/Sqpack/S11Opt" $FIELD_CERTS) > "$WORK/generate.log" 2>&1
if [ -n "${N11_WRITE_MANIFEST:-}" ]; then
  (cd "$P/Sqpack/S11Opt" && for f in Data.lean F00/*.lean F00/Roots.txt Shared/*.lean Own/*.lean \
       F0[1-9]/*.lean F[1-9][0-9]/*.lean; do
     [ ! -f "$f" ] || printf '%s  %s\n' "$(sha "$f")" "$f"; done) > "$HERE/MANIFEST.sha256"
  echo MANIFEST_WRITTEN; exit 0
fi
(cd "$P/Sqpack/S11Opt" && while read -r h f; do
   [ "$(sha "$f")" = "$h" ] || { echo "generated file differs from MANIFEST: $f" >&2; exit 1; }
 done < "$HERE/MANIFEST.sha256")
if grep -rn -e 'sorry' -e 'native_decide' -e '^axiom' "$P/Sqpack/S11Opt"; then
  echo "forbidden construct in overlay" >&2; exit 1
fi
[ -z "${N11_NO_BUILD:-}" ] || { echo N11_DATA_VERIFIED; exit 0; }

# 4. build: Mathlib cache, the upper bound, then the field-00 trees (N11_JOBS at a time)
(cd "$P" && lake exe cache get) > "$WORK/build.log" 2>&1
for t in Sqpack.S11Opt.Upper Sqpack.S11Opt.FieldBridge Sqpack.S11Opt.Cells Sqpack.S11Opt.F00.Data; do
  (cd "$P" && lake build "$t") >> "$WORK/build.log" 2>&1 || { tail -30 "$WORK/build.log"; exit 1; }
done
(cd "$P/Sqpack/S11Opt/F00" && ls Cov*.lean Own*.lean | sed 's/\.lean$//; s/^/Sqpack.S11Opt.F00./') \
  | (cd "$P" && xargs -P "$JOBS" -n 1 lake build) >> "$WORK/build.log" 2>&1 \
  || { tail -30 "$WORK/build.log"; exit 1; }
(cd "$P" && lake build Sqpack.S11Opt.F00.Final) >> "$WORK/build.log" 2>&1 || { tail -30 "$WORK/build.log"; exit 1; }
# the general field certificates (shared grid, ownership trees, covers) and the induction rules
# shared dependencies first, one at a time (parallel lake processes must not build the same module)
for t in Sqpack.S11Opt.Shared.Grid Sqpack.S11Opt.FieldGen Sqpack.S11Opt.Split.U2Rules Sqpack.S11Opt.Split.Frame \
    $(for c in $FIELD_CERTS; do printf 'Sqpack.S11Opt.F%02d.Data ' "$c"; done); do
  (cd "$P" && lake build "$t") >> "$WORK/build.log" 2>&1 || { tail -30 "$WORK/build.log"; exit 1; }
done
(cd "$P/Sqpack/S11Opt" && ls Own/o*.lean F[0-9][0-9]/Cov*P*.lean | grep -v '^F00/' | sed 's/\.lean$//; s#/#.#; s/^/Sqpack.S11Opt./') \
  | (cd "$P" && xargs -P "$JOBS" -n 1 lake build) >> "$WORK/build.log" 2>&1 \
  || { tail -30 "$WORK/build.log"; exit 1; }
for c in $FIELD_CERTS; do
  (cd "$P" && lake build "Sqpack.S11Opt.F$(printf %02d "$c").Final") >> "$WORK/build.log" 2>&1 \
    || { tail -30 "$WORK/build.log"; exit 1; }
done
if grep -q -e '^error' -e ': error' "$WORK/build.log"; then grep -n -e '^error' -e ': error' "$WORK/build.log" | head; exit 1; fi

# 5. axioms
(cd "$P" && lake env lean Sqpack/S11Opt/Axioms.lean) > "$WORK/axioms.log" 2>&1
cat "$WORK/axioms.log"
[ "$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" "$WORK/axioms.log")" = 12 ]
echo N11_LEAN_BUILD_VERIFIED
