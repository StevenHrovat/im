#!/usr/bin/env bash
# arsenal/tools/lint.sh - the gate of every change to the arsenal: it contains nothing that cannot run, so nothing that cannot be
# soundly constructed. Static, no network, no build. Exit 0 or 1.
#
#   1. the toolchain is Lean v4.34.0 and the one requirement is Mathlib at tag v4.34.0;
#   2. every module imports only Mathlib or the arsenal's own modules;
#   3. no module uses an escape hatch (sorry, admit, axiom, native_decide, unsafe, implemented_by, extern, ofReduceBool,
#      skipKernelTC): everything that is stated is constructed and checked by Lean's kernel. A statement left open is answered
#      R136a1 instead (Arsenal/R136a1.lean): a named hypothesis, never an axiom. Only code is read, never comments or strings,
#      so the words stay free for prose;
#   4. every module is reached from Arsenal.lean, so a build of the library builds all of it.
# It lists every part answered R136a1, by name. tools/lint-selftest.sh shows that each rule fails when it should.
# The build and the kernel's axiom report are tools/check.sh (needs Mathlib, about 5 GB).
set -euo pipefail
cd "$(dirname "$0")/.."
bad=0
fail() { echo "FAIL $*"; bad=1; }

# 1. toolchain and the one requirement
[ "$(tr -d '[:space:]' < lean-toolchain)" = "leanprover/lean4:v4.34.0" ] || fail "lean-toolchain is not leanprover/lean4:v4.34.0"
reqs="$(grep -c '^\[\[require\]\]' lakefile.toml || true)"
[ "$reqs" = "1" ] || fail "lakefile.toml has $reqs requirements, the arsenal has exactly one (Mathlib)"
grep -qx 'name = "mathlib"' lakefile.toml || fail "the requirement is not Mathlib"
grep -qx 'rev = "v4.34.0"' lakefile.toml || fail "Mathlib is not pinned to tag v4.34.0"

mapfile -t files < <(find Arsenal -name '*.lean' | sort; echo Arsenal.lean)

# The code of a file: block comments, line comments and string literals blanked, line numbers kept.
code() {
  perl -0777 -pe 's{/-.*?-/}{ (my $c = $&) =~ s/[^\n]//g; $c }gse; s{--[^\n]*}{}g; s{"(?:[^"\\\n]|\\.)*"}{""}g' "$1"
}

# 2. imports
for f in "${files[@]}"; do
  while IFS= read -r m; do
    case "$m" in Mathlib|Mathlib.*|Arsenal.*) ;; *) fail "$f imports $m (only Mathlib and Arsenal.* are allowed)";; esac
  done < <(code "$f" | sed -n 's/^import[[:space:]]\+//p' | tr ' ' '\n' | grep -v '^$' || true)
done

# 3. escape hatches, in code only
hatch='\bsorry\b|\badmit\b|^\s*(private\s+|protected\s+)?axiom\b|\bnative_decide\b|\bunsafe\b|implemented_by|@\[extern|ofReduceBool|skipKernelTC'
for f in "${files[@]}"; do
  hits="$(code "$f" | grep -nE "$hatch" || true)"
  [ -z "$hits" ] || fail "escape hatch in $f, answer the part R136a1 instead: $(echo "$hits" | head -3 | tr '\n' ' ')"
done

# 4. reachability: every Arsenal/X/Y.lean is imported, directly or through another module, from Arsenal.lean.
declare -A seen; queue=(Arsenal)
while [ ${#queue[@]} -gt 0 ]; do
  m="${queue[0]}"; queue=("${queue[@]:1}")
  [ -n "${seen[$m]:-}" ] && continue; seen[$m]=1
  f="$(echo "$m" | tr . /).lean"; [ -f "$f" ] || continue
  for d in $(code "$f" | sed -n 's/^import[[:space:]]\+//p' | tr ' ' '\n' | grep '^Arsenal\.' || true); do queue+=("$d"); done
done
for f in "${files[@]}"; do
  m="$(echo "${f%.lean}" | tr / .)"
  [ -n "${seen[$m]:-}" ] || fail "$f is not reached from Arsenal.lean"
done

[ $bad -eq 0 ] || exit 1

# The parts answered R136a1, by name (in code, so a name in prose is not counted).
outside="$(for f in "${files[@]}"; do perl -0777 -pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g' "$f"; done | grep -oE 'R136a1 "[^"]+"' | sort -u || true)"
n_out="$(printf '%s' "$outside" | grep -c . || true)"
echo "lint: OK (${#files[@]} modules; Mathlib v4.34.0 only; no escape hatch; $n_out part(s) answered R136a1)"
if [ "$n_out" != "0" ]; then printf '%s\n' "$outside" | sed 's/^/  outside: /'; fi
