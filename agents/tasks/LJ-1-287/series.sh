#!/bin/zsh
# LJ-1.287 paired cold-run series, AS IT ACTUALLY RAN.
# ONE agda process at a time, always. Cycles 1 and 2 run the control first.
# Cycle 3 REVERSES the order. Cycle 4 replays [LJ-1.283]'s void seal arm to
# locate its seconds.
set -u
cd /Users/alsg/Agentic/Bedrock
M=agents/tasks/LJ-1-287/measure.sh
# cycle 1
$M ControlEnv     c1 --profile=definitions
$M Bisect         b1 --profile=definitions
$M TreatedNoIter  t1 --profile=definitions
# cycle 2
$M ControlEnv     c2
$M TreatedNoIter  t2 --profile=definitions
$M TreatedNoIter  t3
# cycle 3, order reversed
$M TreatedNoIter  t4
$M ControlEnv     c3
# cycle 4, the seal replay
$M SealReplay     s1 --profile=definitions
echo "SERIES DONE"
