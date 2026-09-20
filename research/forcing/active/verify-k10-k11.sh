#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 ../archive.py prepare
mkdir -p k10-k11-logs

check_slots() {
  announced=0
  while :; do
    processes=$(ps -axo comm) || exit 1
    active=$(printf '%s\n' "$processes" | awk '$0 ~ /(^|\/)agda$/ {n++} END {print n+0}')
    if [ "$active" -lt 2 ]; then
      return
    fi
    if [ "$announced" -eq 0 ]; then
      printf 'Agda slots full; waiting for a free slot.\n'
      announced=1
    fi
    sleep 2
  done
}

count=0
for source in \
  CheckRecursion.agda \
  InternalCheck.agda \
  K9/BooleanSupport.agda \
  K10/CohenCompile.agda \
  K10/CohenValSeam.agda \
  K10/CohenPairUnion.agda \
  K10/CohenZFC.agda \
  K10/CohenBooleanCands.agda \
  K10/CohenBooleanSubset.agda \
  K10/CohenNameIntro.agda \
  K10/CohenBooleanPower.agda \
  K10/CohenBooleanPowerMem.agda \
  K10/CohenBooleanNamed.agda \
  K10/CohenBooleanRename.agda \
  K10/CohenBooleanCheckMem.agda \
  K10/CohenBooleanSubst.agda \
  K10/CohenBooleanDelta0.agda \
  K10/CohenBooleanInductive.agda \
  K10/CohenBooleanSuccApply.agda \
  K10/CohenBooleanInductiveOmega.agda \
  K10/CohenBooleanLeastEmpty.agda \
  K10/CohenBooleanLeastSucc.agda \
  K10/CohenBooleanLeastAll.agda \
  K10/CohenBooleanOmegaLeast.agda \
  K10/CohenBooleanWk1.agda \
  K10/CohenBooleanOmegaTop.agda \
  K10/CohenBooleanOmegaSrc.agda \
  K10/CohenBooleanOmegaEq.agda \
  K10/CohenBooleanPowerSrc.agda \
  K10/CohenBooleanPowerUnfold.agda \
  K10/CohenBooleanPowerWeight.agda \
  K10/CohenBooleanSubsetVal.agda \
  K10/CohenBooleanPowerSub.agda \
  K10/CohenBooleanMiximal.agda \
  K10/CohenBooleanMiximalMem.agda \
  K10/CohenBooleanMiximalCover.agda \
  K10/CohenBooleanMiximalApprox.agda \
  K10/CohenBooleanSubsetLe.agda \
  K10/CohenBooleanMiximalLeft.agda \
  K10/CohenBooleanSubsetMem.agda \
  K10/CohenBooleanInnerBot.agda \
  K10/CohenBooleanInjBot.agda \
  K10/CohenBooleanInjWx.agda \
  K10/CohenBooleanInjSgl.agda \
  K10/CohenBooleanInjSglCong.agda \
  K10/CohenBooleanInjKPairFwd.agda \
  K10/CohenBooleanInjSglUnique.agda \
  K10/CohenBooleanInjKPairRev.agda \
  K10/CohenBooleanInjForce.agda \
  K10/CohenBooleanInjCcc.agda \
  K10/CohenBooleanInjFiber.agda \
  K10/CohenBooleanInjMem.agda \
  K10/CohenBooleanInjCover.agda \
  K10/CohenBooleanInjCheck.agda \
  K10/CohenBooleanInjMaps.agda \
  K10/CohenBooleanInjRn.agda \
  K10/CohenBooleanInjInner.agda \
  K10/CohenBooleanInjTriple.agda \
  K10/CohenBooleanInjAtom.agda \
  K10/CohenBooleanInjPipe.agda \
  K10/CohenBooleanInjCheckτ.agda \
  K10/CohenBooleanInjHit.agda \
  K10/CohenBooleanInjSelect.agda \
  K10/CohenBooleanInjGlue.agda \
  K10/CohenBooleanNotCH.agda \
  K10/CohenBooleanOmegaPart.agda \
  K10/CohenBooleanPowerTop.agda \
  K10/CohenBooleanCHBot.agda \
  K10/CohenTheorem.agda \
  K10/CohenCorrespondence.agda \
  K11/CountableCohen.agda \
  K11/Corollary.agda
do
  check_slots
  name=$(printf '%s' "$source" | tr '/' '_')
  exitcode=0
  GHCRTS='-A64m -I0 -M8g' agda "$source" > "k10-k11-logs/$name.log" 2>&1 || exitcode=$?
  printf '\nEXIT=%s\n' "$exitcode" >> "k10-k11-logs/$name.log"
  printf '%-42s exit=%s\n' "$source" "$exitcode"
  if [ "$exitcode" -ne 0 ]; then
    sed -n '1,100p' "k10-k11-logs/$name.log"
    exit "$exitcode"
  fi
  count=$((count + 1))
done

check_negative() {
  check_slots
  fixture=$1
  pattern=$2
  exitcode=0
  GHCRTS='-A64m -I0 -M8g' agda "Controls/Negative/$fixture.agda" > "k10-k11-logs/$fixture.log" 2>&1 || exitcode=$?
  printf '\nEXIT=%s\n' "$exitcode" >> "k10-k11-logs/$fixture.log"
  if [ "$exitcode" -ne 42 ] || ! grep -F -q "$pattern" "k10-k11-logs/$fixture.log" || ! grep -F -q '[UnequalTerms]' "k10-k11-logs/$fixture.log"; then
    sed -n '1,100p' "k10-k11-logs/$fixture.log"
    printf 'Negative control %s did not fail as expected.\n' "$fixture"
    exit 1
  fi
  printf '%s: expected exit 42 and type error verified.\n' "$fixture"
}

check_negative MissingFunction 'PB.countable-from-ccc₂'
check_negative MissingValueFunction 'Proof.functionFo'
check_negative MissingCheckReading 'chkFo'
check_negative MissingOnto 'OrderType.Onto'
printf '%s positive endpoint modules and four expected-failure controls verified.\n' "$count"
