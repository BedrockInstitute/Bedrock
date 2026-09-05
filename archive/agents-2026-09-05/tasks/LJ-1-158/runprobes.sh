#!/bin/zsh
# LJ-1.158 probe series. ONE agda at a time, cold every run, warm-up discarded.
set -u
D=agents/tasks/LJ-1-158
R=$D/runs
mkdir -p $R
run () {  # run <probe> <tag>
  rm -f _build/2.8.0/agda/agents/tasks/LJ-1-158/ProbeLJ1158$1.agdai
  echo "# load before $(uptime)" > $R/$1.$2.txt
  s=$(date +%s.%N)
  agda --profile=internal $D/ProbeLJ1158$1.agda >> $R/$1.$2.txt 2>&1
  e=$?
  f=$(date +%s.%N)
  echo "# exit $e" >> $R/$1.$2.txt
  echo "# wall $(echo "$f - $s" | bc)" >> $R/$1.$2.txt
  echo "# load after $(uptime)" >> $R/$1.$2.txt
  echo "$1 $2: exit $e wall $(echo "$f - $s" | bc)"
}
run L1 warmup
for t in run1 run2; do run L1 $t; run L2 $t; done
