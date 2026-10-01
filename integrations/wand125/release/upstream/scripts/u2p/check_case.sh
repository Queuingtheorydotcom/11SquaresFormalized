#!/bin/sh
# Lean check of one generated case on the VM: Data, the step trees (P in parallel), Main, axioms.
# Usage: sh check_case.sh CASE P
c=$1; P=${2:-4}
export PATH=$HOME/.elan/bin:$PATH
cd $HOME/n11u2p
D=Sqpack/S11Opt/Split/U2P/C$c
rm -rf $D; mkdir -p $D $HOME/check_out
cp $HOME/gen_out/C$c/*.lean $D/
log=$HOME/check_out/C$c.log
: > $log
t0=$(date +%s)
lake build Sqpack.S11Opt.Split.U2P.C$c.Data >> $log 2>&1 || { echo "C$c FAIL Data" > $HOME/check_out/C$c.result; exit 1; }
for pat in '^S[0-9]*_p[0-9]*\.lean$' '^S[0-9]*\.lean$'; do     # part files first, then the steps
ls $D | grep "$pat" | sed "s/\.lean$//; s/^/Sqpack.S11Opt.Split.U2P.C$c./" \
  | xargs -P $P -n 1 sh -c 'lake build "$0" > '"$HOME"'/check_out/$0.log 2>&1 || echo "FAIL $0" >> '"$log"
done
if grep -q FAIL $log; then echo "C$c FAIL trees" > $HOME/check_out/C$c.result; exit 1; fi
lake build Sqpack.S11Opt.Split.U2P.C$c.Main >> $log 2>&1 || { echo "C$c FAIL Main" > $HOME/check_out/C$c.result; exit 1; }
printf 'import Sqpack.S11Opt.Split.U2P.C%s.Main\n#print axioms SquarePacking.S11Opt.Split.U2P.C%s.excluded\n' $c $c > /tmp/ax$c.lean
ax=$(lake env lean /tmp/ax$c.lean 2>&1)
echo "C$c OK $(( $(date +%s) - t0 ))s $ax" > $HOME/check_out/C$c.result
