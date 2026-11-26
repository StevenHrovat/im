#!/usr/bin/env bash
# arsenal/card-check/card-check.sh - the card check: what a Lean project states is well-formed, rests on nothing it does not
# name, and shows its route. Exit 0 or 1.
#
#   card-check.sh <project-dir> <Module> [<Module> ...]
#
# For the Lake project in <project-dir> (Lean and Mathlib, any version the project pins) and the modules named:
#   1. well-formed: the modules build (every statement elaborates against the project's Mathlib, or the build fails);
#   2. no escape hatch in their source (sorry, admit, axiom, native_decide, unsafe, implemented_by, extern, ofReduceBool,
#      skipKernelTC; code only, never comments or strings): the same rule as arsenal/tools/lint.sh, rule 3;
#   3. the kernel's axiom report: every declaration of the modules rests on propext, Quot.sound, Classical.choice at most;
#   4. the route of every declaration: the outside inputs its statement names (`R136a1 "name" P`, the arsenal's one way to
#      leave a statement open, seen through the definitions of the checked modules and of the arsenal), and its derivation
#      (the declarations of the checked modules and of the arsenal its proof uses directly); a declaration of type
#      `Arsenal.Problems.Card` is listed as a card.
# What it cannot do, by a theorem and not a gap: decide whether a statement is true, or find a proof. A card the check passes is
# well-formed and honest about what it rests on; it is solved only where a proof is there.
# The report is written to <project-dir>/card-check-report/report.txt.
set -euo pipefail
[ $# -ge 2 ] || { echo "usage: card-check.sh <project-dir> <Module> [<Module> ...]" >&2; exit 2; }
proj="$1"; shift
cd "$proj"
mods=("$@")
bad=0
fail() { echo "FAIL $*"; bad=1; }

# 1. well-formed: the build
lake build "${mods[@]}"

# 2. escape hatches, in code only
code() {
  perl -0777 -pe 's{/-.*?-/}{ (my $c = $&) =~ s/[^\n]//g; $c }gse; s{--[^\n]*}{}g; s{"(?:[^"\\\n]|\\.)*"}{""}g' "$1"
}
hatch='\bsorry\b|\badmit\b|^\s*(private\s+|protected\s+)?axiom\b|\bnative_decide\b|\bunsafe\b|implemented_by|@\[extern|ofReduceBool|skipKernelTC'
for m in "${mods[@]}"; do
  f="$(echo "$m" | tr . /).lean"
  [ -f "$f" ] || { fail "no source file $f for module $m"; continue; }
  hits="$(code "$f" | grep -nE "$hatch" || true)"
  [ -z "$hits" ] || fail "escape hatch in $f, answer the part R136a1 instead: $(echo "$hits" | head -3 | tr '\n' ' ')"
done
[ $bad -eq 0 ] || exit 1

# 3 and 4. the kernel's axiom report and the route
mkdir -p card-check-report
modlist="$(printf '`%s,' "${mods[@]}" | sed 's/,$//')"
{
  echo "import Lean"
  for m in "${mods[@]}"; do echo "import $m"; done
  cat <<LEAN
open Lean

/-- In scope: the checked modules and the arsenal's. Their definitions are unfolded to find outside inputs; their declarations
count as derivation steps. -/
def inScope (env : Environment) (mods : List Name) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => let m := env.header.moduleNames[idx.toNat]!; mods.contains m || m.getRoot == \`Arsenal
  | none => false

/-- The outside inputs an expression names: every \`R136a1 "name" _\`, through the in-scope definitions it mentions. -/
partial def outside (env : Environment) (mods : List Name) (e : Expr) : StateM (NameSet × Array String) Unit := do
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf \`Arsenal.R136a1 && args.size ≥ 1 then
      match args[0]! with
      | .lit (.strVal s) => modify fun (v, a) => (v, if a.contains s then a else a.push s)
      | _ => modify fun (v, a) => (v, if a.contains "(a name given as a parameter)" then a else a.push "(a name given as a parameter)")
    outside env mods fn
    for a in args do outside env mods a
  | .const n _ =>
    if (← get).1.contains n then return
    modify fun (v, a) => (v.insert n, a)
    if inScope env mods n then
      if let some (.defnInfo d) := env.find? n then outside env mods d.value
  | .lam _ t b _ | .forallE _ t b _ => do outside env mods t; outside env mods b
  | .letE _ t v b _ => do outside env mods t; outside env mods v; outside env mods b
  | .mdata _ b | .proj _ _ b => outside env mods b
  | _ => pure ()

#eval show CoreM Unit from do
  let env ← getEnv
  let mods : List Name := [$modlist]
  let mut n := 0
  let mut nonstd := 0
  let mut cards := 0
  let decls := env.constants.map₁.toList.filter fun (nm, _) =>
    !nm.isInternal && match env.getModuleIdxFor? nm with
      | some idx => mods.contains env.header.moduleNames[idx.toNat]!
      | none => false
  for (nm, ci) in decls.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    let axs ← Lean.collectAxioms nm
    let std := axs.all (fun a => a == \`\`propext || a == \`\`Classical.choice || a == \`\`Quot.sound)
    n := n + 1
    unless std do nonstd := nonstd + 1
    IO.println s!"{if std then "ok" else "NONSTD"} {nm} {axs}"
    if ci.type.isConstOf \`Arsenal.Problems.Card then
      cards := cards + 1
      IO.println s!"  card"
    let (_, (_, outs)) := (outside env mods ci.type).run ({}, #[])
    for o in outs do IO.println s!"  outside: {o}"
    if let some v := ci.value? (allowOpaque := true) then
      let uses := v.getUsedConstants.filter fun c => c != nm && !c.isInternal && inScope env mods c
      if !uses.isEmpty then IO.println s!"  uses: {uses.toList}"
  IO.println s!"COUNT {n} NONSTD {nonstd} CARDS {cards}"
LEAN
} > card-check-report/Report.lean
lake env lean card-check-report/Report.lean > card-check-report/report.txt 2>&1 || true
if ! grep -q '^COUNT' card-check-report/report.txt; then cat card-check-report/report.txt; echo "FAIL the report did not run"; exit 1; fi
sum="$(grep '^COUNT' card-check-report/report.txt)"
read -r _ count _ nonstd _ ncards <<< "$sum"
if [ "$nonstd" != "0" ]; then grep '^NONSTD' card-check-report/report.txt; echo "FAIL $nonstd declaration(s) rest on more than propext, Quot.sound, Classical.choice"; exit 1; fi
echo "== outside inputs named (R136a1)"
grep '^  outside:' card-check-report/report.txt | sed 's/^  outside: /  /' | sort -u || true
echo "OK card check: $count declarations in ${#mods[@]} module(s), $ncards card(s); none rests on more than propext, Quot.sound, Classical.choice; route and derivation in card-check-report/report.txt"
