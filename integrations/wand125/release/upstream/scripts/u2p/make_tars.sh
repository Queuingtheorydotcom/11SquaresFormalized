#!/bin/sh
# Reproducible per-case archives n11-u2p-C<4 digits>.tar.xz of the kernel-checked files.
# Usage: sh make_tars.sh OUTDIR CASE...
out=$1; shift
mkdir -p $out
cd $HOME/n11u2p
for c in "$@"; do
  name=$(printf "n11-u2p-C%04d.tar.xz" $c)
  tar --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner -cf - Sqpack/S11Opt/Split/U2P/C$c \
    | xz -6 -T0 > $out/$name
done
