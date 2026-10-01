#!/bin/sh
# Check every generated OK case once (one case at a time, P trees in parallel), until STOP exists.
P=${1:-2}
while [ ! -f $HOME/STOP ]; do
  next=""
  for c in $(grep '"status": "OK"' $HOME/gen_out/summary.jsonl | sed 's/.*"case": \([0-9]*\).*/\1/'); do
    [ -f $HOME/check_out/C$c.result ] || [ -f $HOME/check_out/C$c.running ] || { next=$c; break; }
  done
  if [ -z "$next" ]; then sleep 60; continue; fi
  touch $HOME/check_out/C$next.running
  sh $HOME/check_case.sh $next $P
  rm -f $HOME/check_out/C$next.running
done
