#!/bin/bash
# LJ-1.209: THE DISCRIMINATOR SERIES, and it also reverses the arm order.
# Series 1 ran plain-then-seal in every pair, so the load decay across the
# series always favoured the seal.  Here the new arm goes FIRST in every pair.
# ProbeTrivial keeps the extra telescope component and throws the numeral
# content away.  It answers: does the 8.4 s follow the CONTENT or the
# COMPONENT?
cd /Users/alsg/Agentic/Bedrock
for i in 1 2 3; do
  bash agents/tasks/LJ-1-209/run_one.sh ProbeTrivial "t$i"
  bash agents/tasks/LJ-1-209/run_one.sh ProbePlain "q$i"
done
echo "SERIES 2 DONE"
