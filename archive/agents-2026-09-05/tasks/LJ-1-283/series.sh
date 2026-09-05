#!/bin/zsh
# LJ-1.283 paired cold-run series. ONE agda process at a time, always.
# Order is REVERSED between cycles so a position effect shows as a
# between-cycle split inside one arm ([LJ-1.215]'s law, [LJ-1.275]'s design).
set -u
cd /Users/alsg/Agentic/Bedrock
M=agents/tasks/LJ-1-283/measure.sh
$M ControlEnv     c1
$M TreatedBridge  t1
$M TreatedBridge  t2
$M ControlEnv     c2
$M ControlEnv     c3
$M TreatedBridge  t3
echo "SERIES DONE"
