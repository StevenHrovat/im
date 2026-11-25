#!/usr/bin/env bash
# tools/trust-roundtrip.sh - every hash IM trusts is first proven by rotation, back and then forth, and each step must deliver the
# expected value (the first author's rule, 2026-11-25: "any sha that is trusted has to first be positively proven through rotation").
# It runs before every commit and push (.githooks) and in the verify workflow (tools/verify), so nothing is written that cannot be read
# back. Ported from Gravity's tools/trust-roundtrip.sh and extended to IM's Externals.
#
#   back   from the content to the hash: the hash is recomputed from what it names
#   forth  from the hash to the content: the content is fetched by its hash (git checks every object id on arrival) and must give
#          the same hash again
#
# First a canary: the full turn on vxunderground must return it, or the state is smelly and nothing is trusted.
# What it proves, found by itself so that a new pin is covered by construction:
#   vendor/*/PIN                  the sha256 of the held copy (back), and the pinned commit rebuilt into the same copy, byte for byte (forth)
#                                 (also a held copy's own held copies, vendor/*/vendor/*/PIN)
#   externals/EXTERNALS (git)     every commit id (fetched by its id, the id recomputed from its content)
#   lakefile.toml requires        a tag must resolve to the commit the lake manifest next to it records
#   lake-manifest.json packages   every package's commit id (Mathlib and everything it needs)
#   .github/workflows             every action pinned by a commit id; an action trusted by a movable tag fails
# The archive rows of externals/EXTERNALS (the Lean toolchain) are downloads of about 200 MB: their sha256 is recomputed by
# `tools/rebuild supply`, which every minting needs. Fetched objects are cached in .reproduce/trust (TRUST_CACHE); without the cache
# and without network the check fails, so nothing is trusted unproven. Exit 0 only when every proof passes.
set -uo pipefail
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_PREFIX GIT_COMMON_DIR GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES
cd "$(cd "$(dirname "$0")/.." && pwd)"
export LC_ALL=C
CACHE=${TRUST_CACHE:-$PWD/.reproduce/trust}
mkdir -p "$CACHE"
fail=0; count=0
ok() { echo "ok   $*"; count=$((count + 1)); }
bad() { echo "FAIL $*"; fail=1; }
is_sha() { [[ "$1" =~ ^[0-9a-f]{40}$ ]]; }

# The folder hash of tools/check-pin.sh: every file but PIN, in ordinal path order, each as "<relative path>\n<bytes>".
hash_folder() {
  local folder="$1"
  { while IFS= read -r -d '' f; do printf '%s\n' "${f#"$folder"/}"; cat "$f"; done \
      < <(find "$folder" -type f ! -path "$folder/PIN" -print0 | sort -z); } | sha256sum | cut -d' ' -f1
}
cache_for() {
  local url="$1" d
  d="$CACHE/$(printf '%s' "${url%.git}" | sha256sum | cut -c1-16)"
  if [ ! -d "$d" ]; then
    git init -q --bare "$d"
    git -C "$d" remote add origin "$url"
    git -C "$d" config remote.origin.promisor true
  fi
  printf '%s' "$d"
}
fetch_commit() {
  local d="$1" sha="$2" filter="$3"
  git -C "$d" cat-file -e "$sha^{commit}" 2>/dev/null && return 0
  if [ -n "$filter" ]; then git -C "$d" fetch -q --depth 1 --filter="$filter" origin "$sha" 2>/dev/null
  else git -C "$d" fetch -q --depth 1 origin "$sha" 2>/dev/null; fi
}
commit_back() {
  local d="$1" sha="$2"
  [ "$(git -C "$d" cat-file commit "$sha" | git -C "$d" hash-object -t commit --stdin)" = "$sha" ]
}
roundtrip_commit() {
  local what="$1" url="$2" sha="$3" filter="$4" d
  d=$(cache_for "$url")
  if ! fetch_commit "$d" "$sha" "$filter"; then bad "$what: commit $sha could not be fetched from $url (no network and not cached)"; return; fi
  if ! commit_back "$d" "$sha"; then bad "$what: the content of commit $sha does not hash back to it"; return; fi
  ok "$what: commit ${sha:0:12} fetched by its id, its id recomputed from its content ($url)"
}

# 0. The canary (Gravity's Draft 5, Appendix T.5).
rot13() { tr 'abcdefghijklmnopqrstuvwxyz' 'nopqrstuvwxyzabcdefghijklm'; }
once=$(printf '%s' vxunderground | rot13); twice=$(printf '%s' "$once" | rot13)
if [ "$once" = ikhaqretebhaq ] && [ "$twice" = vxunderground ]; then
  ok "canary: the full turn on vxunderground returns it (ikhaqretebhaq, then vxunderground); the state is not smelly"
else
  echo "SMELLY: the full turn on vxunderground does not return it (got '$once', then '$twice'); nothing is trusted in this state"
  exit 1
fi

# 1. Held copies: the content's sha256 (back), then the pinned commit rebuilt into the same copy (forth).
# Nested held copies (a held repository holds its own copies) are proven the same way: vendor/<name>/vendor/<name>/.
for folder in vendor/*/ vendor/*/vendor/*/; do
  [ -d "$folder" ] || continue
  folder="${folder%/}"; pin="$folder/PIN"
  [ -f "$pin" ] || { bad "$folder has no PIN"; continue; }
  src=$(awk -F'\t' '$1=="source"{print $2}' "$pin"); commit=$(awk -F'\t' '$1=="commit"{print $2}' "$pin")
  want=$(awk -F'\t' '$1=="sha256"{print $2}' "$pin")
  have=$(hash_folder "$folder")
  if [ "$have" != "$want" ]; then bad "$folder back: the content hashes to $have, the PIN says $want"; continue; fi
  ok "$folder back: the content hashes to the PIN's sha256 ${want:0:12}"
  is_sha "$commit" || { bad "$folder: the PIN's commit '$commit' is not a commit id"; continue; }
  before=$fail
  roundtrip_commit "$folder PIN commit" "$src" "$commit" ""
  [ "$fail" = "$before" ] || continue
  d=$(cache_for "$src"); tmp=$(mktemp -d)
  if git -C "$d" -c core.autocrlf=false -c core.eol=lf archive "$commit" | tar -x -C "$tmp"; then
    rm -rf "$tmp/.github"
    rebuilt=$(hash_folder "$tmp")
    if [ "$rebuilt" != "$want" ]; then bad "$folder forth: the commit rebuilds to $rebuilt, the PIN says $want"
    elif ! diff -r --exclude=PIN "$tmp" "$folder" >/dev/null; then bad "$folder forth: the rebuilt copy differs from the held files"
    else ok "$folder forth: commit ${commit:0:12} rebuilds the held copy byte for byte, sha256 ${want:0:12}"; fi
  else bad "$folder forth: commit $commit could not be read back"; fi
  rm -rf "$tmp"
done

# 2. The Externals with a commit pin.
while IFS=$'\t' read -r name kind src pin _; do
  case "$name" in ''|\#*) continue;; esac
  case "$kind" in
    git) is_sha "$pin" || { bad "external $name: the pin '$pin' is not a commit id"; continue; }
         roundtrip_commit "external $name" "$src" "$pin" "tree:0";;
    archive) [[ "$pin" =~ ^[0-9a-f]{64}$ ]] || bad "external $name: the pin '$pin' is not a sha256";;
    *) bad "external $name: unknown kind '$kind'";;
  esac
done < externals/EXTERNALS

# 3. Lake: a required tag resolves to the commit the manifest records; every package of a manifest round trips. The held copies
#    (vendor/) are proven as a whole above.
manifest_rev() { jq -r --arg n "$2" '.packages[] | select(.name == $n) | .rev' "$1" 2>/dev/null | tr -d '\r' | head -1; }
while IFS= read -r lf; do
  dir=$(dirname "$lf"); man="$dir/lake-manifest.json"
  while IFS=$'\t' read -r name url rev; do
    [ -n "$url" ] || continue
    is_sha "$rev" && continue   # a commit pin is proven with the manifest below
    recorded=$(manifest_rev "$man" "$name")
    is_sha "$recorded" || { bad "$lf $name: trusted by the tag '$rev' with no commit recorded in $man"; continue; }
    resolved=$(git ls-remote "$url" "refs/tags/$rev^{}" 2>/dev/null | awk '{print $1}' | head -1)
    [ -n "$resolved" ] || resolved=$(git ls-remote "$url" "refs/tags/$rev" 2>/dev/null | awk '{print $1}' | head -1)
    if [ -z "$resolved" ]; then bad "$lf $name: the tag '$rev' could not be resolved at $url"; continue; fi
    if [ "$resolved" != "$recorded" ]; then bad "$lf $name: the tag '$rev' resolves to $resolved, the manifest records $recorded"; continue; fi
    ok "$lf $name: the tag '$rev' resolves to the recorded ${recorded:0:12}"
  done < <(awk '
    /^\[\[/ { if (req && n != "") print n "\t" g "\t" r; req = ($0 ~ /^\[\[require\]\]/); n = ""; g = ""; r = ""; next }
    req && /^name = / { v = $0; sub(/^name = "/, "", v); sub(/".*/, "", v); n = v }
    req && /^git = /  { v = $0; sub(/^git = "/, "", v);  sub(/".*/, "", v); g = v }
    req && /^rev = /  { v = $0; sub(/^rev = "/, "", v);  sub(/".*/, "", v); r = v }
    END { if (req && n != "") print n "\t" g "\t" r }' "$lf")
done < <(git ls-files '*lakefile.toml' | grep -v '^vendor/')
while IFS= read -r man; do
  while IFS=$'\t' read -r name url rev; do
    is_sha "$rev" || { bad "$man $name: the package is not pinned by a commit id ('$rev')"; continue; }
    roundtrip_commit "$man $name" "$url" "$rev" "tree:0"
  done < <(jq -r '.packages[] | select(.type == "git") | [.name, .url, .rev] | @tsv' "$man" | tr -d '\r')
done < <(git ls-files '*lake-manifest.json' | grep -v '^vendor/')

# 4. CI actions: pinned by a commit id and proven, or refused.
while read -r ref; do
  action=${ref%@*}; at=${ref##*@}; repo=$(printf '%s' "$action" | cut -d/ -f1-2)
  if is_sha "$at"; then roundtrip_commit "action $action" "https://github.com/$repo" "$at" "tree:0"
  else bad "action $action: trusted by the movable tag '$at', not by a hash"; fi
done < <(grep -rhoE "uses: [^ ]+" .github/workflows/ 2>/dev/null | sed 's/^uses: //' | sort -u)

if [ "$fail" = 0 ]; then echo "trust-roundtrip: OK, $count proofs, every trusted hash proven back and forth"
else echo "trust-roundtrip: FAILED (see the lines above); nothing may be written until every trusted hash is proven"; fi
exit $fail
