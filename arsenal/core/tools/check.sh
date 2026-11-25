#!/usr/bin/env bash
# arsenal/core/tools/check.sh - the finite layer, on Lean's kernel alone: no requirement, imports only its own modules, no escape
# hatch; then the build (seconds, nothing to download) and the kernel's axiom report for every declaration. Exit 0 or 1.
# Needs lake and lean on the PATH (vendor/dmp/SETUP.md; tools/lean-install.sh). tools/verify runs it, so the verify workflow does.
set -euo pipefail
cd "$(dirname "$0")/.."
bad=0
fail() { echo "FAIL $*"; bad=1; }
[ "$(tr -d '[:space:]' < lean-toolchain)" = "leanprover/lean4:v4.34.0" ] || fail "lean-toolchain is not leanprover/lean4:v4.34.0"
if grep -q '^\[\[require\]\]' lakefile.toml; then fail "lakefile.toml has a requirement; the core has none"; fi
mapfile -t files < <(find ArsenalCore -name '*.lean' | sort; echo ArsenalCore.lean)
# The code of a file: block comments, line comments and string literals blanked.
code() {
  perl -0777 -pe 's{/-.*?-/}{ (my $c = $&) =~ s/[^\n]//g; $c }gse; s{--[^\n]*}{}g; s{"(?:[^"\\\n]|\\.)*"}{""}g' "$1"
}
for f in "${files[@]}"; do
  while read -r imp; do
    case "$imp" in ArsenalCore|ArsenalCore.*) ;; *) fail "$f imports $imp; the core imports only its own modules" ;; esac
  done < <(code "$f" | sed -n 's/^import \([A-Za-z0-9_.]*\).*/\1/p')
  if code "$f" | grep -qwE 'sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|ofReduceBool|skipKernelTC'; then
    fail "$f uses an escape hatch"
  fi
done
[ "$bad" = 0 ] || exit 1
lake build 2>&1 | tail -1
mkdir -p report
mods="$(find ArsenalCore -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g' | sed 's/^/`/' | paste -sd, -)"
{
  echo 'import Lean'
  echo 'import ArsenalCore'
  echo 'open Lean Elab Command'
  echo '#eval show CoreM Unit from do'
  echo '  let env ← getEnv'
  echo "  let mods : List Name := [$mods]"
  echo '  let mut n := 0'
  echo '  for (nm, _) in env.constants.map₁.toList do'
  echo '    match env.getModuleIdxFor? nm with'
  echo '    | some idx =>'
  echo '      if mods.contains env.header.moduleNames[idx.toNat]! && !nm.isInternal then'
  echo '        let axs ← Lean.collectAxioms nm'
  echo '        n := n + 1'
  echo '        let std := axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)'
  echo '        IO.println s!"{if std then "ok" else "NONSTD"} {nm} {axs}"'
  echo '    | none => pure ()'
  echo '  IO.println s!"COUNT {n}"'
} > report/Report.lean
lake env lean report/Report.lean > report/axioms.txt 2>&1
if grep -q '^NONSTD' report/axioms.txt || ! grep -q '^COUNT' report/axioms.txt; then cat report/axioms.txt; echo "FAIL see above"; exit 1; fi
echo "OK core: $(sed -n 's/^COUNT //p' report/axioms.txt) declarations on Lean's kernel alone, no requirement, none resting on more than propext, Quot.sound, Classical.choice; $(grep -c ' #\[\]$' report/axioms.txt) on no axiom at all"
