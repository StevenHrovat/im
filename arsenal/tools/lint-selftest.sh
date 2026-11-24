#!/usr/bin/env bash
# arsenal/tools/lint-selftest.sh - shows that the lint fails when it should and passes when it should, on a scratch copy.
# The bad cases are named R136a1, as in DMP, so a planted failure is told apart from a real one at a glance. Exit 0 or 1.
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
bad=0
copy() { rm -rf "$tmp/a"; mkdir -p "$tmp/a"; cp -r "$here/Arsenal" "$here/Arsenal.lean" "$here/lakefile.toml" "$here/lean-toolchain" "$here/tools" "$tmp/a/"; }
expect_fail() { # $1 = case, $2 = text the lint must print
  if out="$(bash "$tmp/a/tools/lint.sh" 2>&1)"; then echo "SELFTEST FAIL $1: the lint passed"; bad=1
  elif ! grep -qF -- "$2" <<<"$out"; then echo "SELFTEST FAIL $1: expected '$2' in: $out"; bad=1
  else echo "selftest ok: $1"; fi
}

copy; printf 'import Mathlib\nimport R136a1\n' > "$tmp/a/Arsenal/R136a1Import.lean"; echo 'import Arsenal.R136a1Import' >> "$tmp/a/Arsenal.lean"
expect_fail "an import from outside" "imports R136a1"

copy; printf 'theorem R136a1_planted : 1 = 1 := by sorry\n' > "$tmp/a/Arsenal/R136a1Hatch.lean"; echo 'import Arsenal.R136a1Hatch' >> "$tmp/a/Arsenal.lean"
expect_fail "an escape hatch in code" "escape hatch in Arsenal/R136a1Hatch.lean"

copy; printf 'axiom R136a1_planted : False\n' > "$tmp/a/Arsenal/R136a1Axiom.lean"; echo 'import Arsenal.R136a1Axiom' >> "$tmp/a/Arsenal.lean"
expect_fail "an axiom" "escape hatch in Arsenal/R136a1Axiom.lean"

copy; printf 'import Mathlib\n' > "$tmp/a/Arsenal/R136a1Unreached.lean"
expect_fail "a module not reached from Arsenal.lean" "R136a1Unreached.lean is not reached"

copy; printf '[[require]]\nname = "R136a1"\ngit = "x"\n' >> "$tmp/a/lakefile.toml"
expect_fail "a second requirement" "requirements"

copy; printf '/-! The word sorry in prose, and axiom too. -/\n-- sorry\ndef R136a1_prose : String := "sorry"\ntheorem R136a1_slot (h : Arsenal.R136a1 "planted slot" (1 = 1)) : 1 = 1 := h\n' > "$tmp/a/Arsenal/R136a1Prose.lean"
echo 'import Arsenal.R136a1Prose' >> "$tmp/a/Arsenal.lean"
if out="$(bash "$tmp/a/tools/lint.sh" 2>&1)" && grep -qF 'outside: R136a1 "planted slot"' <<<"$out"; then echo "selftest ok: prose passes, the R136a1 slot is listed"
else echo "SELFTEST FAIL prose: $out"; bad=1; fi

[ $bad -eq 0 ] || exit 1
echo "lint-selftest: OK"
