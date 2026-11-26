#!/usr/bin/env bash
# arsenal/card-check/selftest.sh - the card check fails when it should and passes when it should, on modules planted in the
# arsenal for the run and removed after it (needs the arsenal built against Mathlib, as tools/check.sh does).
#   1. a `sorry` in a checked module: refused by the source scan;
#   2. an axiom declared in an unchecked module and used in a checked one: refused by the kernel's axiom report;
#   3. a card with its outside input named R136a1: passes, the card and the input listed, its credit root GRH by reading;
#   4. Arsenal.Problems: RH's route through the GRH ladder has its credit root GRH derived.
set -euo pipefail
cd "$(dirname "$0")/.."
dir=Arsenal/CardCheckSelftest
trap 'rm -rf "$dir" card-check-report .lake/build/lib/lean/Arsenal/CardCheckSelftest .lake/build/ir/Arsenal/CardCheckSelftest' EXIT
mkdir -p "$dir"
run() { card-check/card-check.sh . "$@" > "$dir/out.txt" 2>&1; }
expect_fail() { if run "$@"; then cat "$dir/out.txt"; echo "selftest FAIL: $1 passed, it must fail"; exit 1; fi; grep -q "$2" "$dir/out.txt" || { cat "$dir/out.txt"; echo "selftest FAIL: $1 failed for another reason"; exit 1; }; echo "selftest ok: $1 refused ($2)"; }

printf '%s\n' 'import Mathlib' 'theorem planted_sorry : (1 : ℕ) = 2 := by sorry' > "$dir/Sorry.lean"
expect_fail Arsenal.CardCheckSelftest.Sorry 'escape hatch'

printf '%s\n' 'import Mathlib' 'axiom planted_axiom : (1 : ℕ) = 2' > "$dir/Ax.lean"
printf '%s\n' 'import Arsenal.CardCheckSelftest.Ax' 'theorem uses_axiom : (1 : ℕ) = 2 := planted_axiom' > "$dir/UsesAx.lean"
expect_fail Arsenal.CardCheckSelftest.UsesAx 'NONSTD'

printf '%s\n' 'import Arsenal.Problems' 'open Arsenal Arsenal.Problems' \
  'def twoPrimes : Card := ⟨"two is prime", Nat.Prime 2, .mathlib⟩' \
  'theorem twoPrimes_certified (h : R136a1 "planted outside input" twoPrimes.Statement) :' \
  '    twoPrimes.observable.box.DMPComplete () := twoPrimes.certified h' > "$dir/Good.lean"
run Arsenal.CardCheckSelftest.Good || { cat "$dir/out.txt"; echo "selftest FAIL: a good card was refused"; exit 1; }
grep -q '1 card(s)' "$dir/out.txt" && grep -q 'planted outside input' "$dir/out.txt" \
  || { cat "$dir/out.txt"; echo "selftest FAIL: the card or its input is not listed"; exit 1; }
echo "selftest ok: a good card passes, the card and its outside input listed"
grep -q 'credit: DMP.GRH.Problems.CardCheckSelftest.Good.twoPrimes (GRH: reading)\|credit: DMP.GRH.*twoPrimes (GRH: reading)' card-check-report/report.txt \
  || { grep credit card-check-report/report.txt | head; echo "selftest FAIL: the good card's credit path is not DMP.GRH. by reading"; exit 1; }
echo "selftest ok: a card that does not use GRH has the credit root GRH by reading"
run Arsenal.Problems || { cat "$dir/out.txt"; echo "selftest FAIL: Arsenal.Problems was refused"; exit 1; }
grep -q 'credit: DMP.GRH.R136a1.RHLibrary.Problems.riemann_of_library (GRH: derived)' card-check-report/report.txt \
  || { grep -A6 'riemann_of_library' card-check-report/report.txt | head; echo "selftest FAIL: RH's route through GRH is not derived"; exit 1; }
echo "selftest ok: RH's route through the arsenal's GRH ladder has the credit root GRH derived"
echo "card-check selftest: OK"
