#!/usr/bin/env bash
# arsenal/tools/check.sh - the full check: the lint, the build against Mathlib, then the kernel's axiom report for every
# declaration of the arsenal. Passes only when every one rests on nothing beyond propext, Quot.sound, Classical.choice.
# Needs lake and lean on the PATH (vendor/dmp/SETUP.md says how) and Mathlib's prebuilt files (lake exe cache get, about 5 GB).
set -euo pipefail
cd "$(dirname "$0")/.."
tools/lint.sh
[ -d .lake/packages/mathlib/.lake/build ] || lake exe cache get
lake build
mkdir -p report
mods="$(find Arsenal -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g' | sed 's/^/`/' | paste -sd, -)"
cat > report/Report.lean <<LEAN
import Arsenal
open Lean Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let mods : List Name := [$mods]
  let mut n := 0
  for (nm, _) in env.constants.map₁.toList do
    match env.getModuleIdxFor? nm with
    | some idx =>
      if mods.contains env.header.moduleNames[idx.toNat]! && !nm.isInternal then
        let axs ← Lean.collectAxioms nm
        n := n + 1
        let std := axs.all (fun a => a == \`\`propext || a == \`\`Classical.choice || a == \`\`Quot.sound)
        IO.println s!"{if std then "ok" else "NONSTD"} {nm} {axs}"
    | none => pure ()
  IO.println s!"COUNT {n}"
LEAN
lake env lean report/Report.lean > report/axioms.txt 2>&1
if grep -q '^NONSTD' report/axioms.txt || ! grep -q '^COUNT' report/axioms.txt; then cat report/axioms.txt; echo "FAIL see above"; exit 1; fi
echo "OK $(sed -n 's/^COUNT //p' report/axioms.txt) declarations, none resting on more than propext, Quot.sound, Classical.choice"
