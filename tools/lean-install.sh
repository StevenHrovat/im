#!/usr/bin/env bash
# tools/lean-install.sh - puts the pinned Lean toolchain on this machine (vendor/dmp/SETUP.md, install steps L1 and L2).
#
#   tools/lean-install.sh [<dir>]      default dir: ~/.im-lean; prints the bin folder to put on the PATH
#
# L2 first (the GitHub release asset of the version in proof/lean-toolchain, checked against the sha256 the setup file records), through
# curl when curl may fetch it, else through Python's urllib and zstandard; nothing else is installed. Idempotent: a present toolchain is kept.
set -euo pipefail
cd "$(dirname "$0")/.."
tc="$(tr -d '[:space:]' < proof/lean-toolchain)"; ver="${tc##*:}"; num="${ver#v}"
dir="${1:-$HOME/.im-lean}"; bin="$dir/lean-$num-linux/bin"
if [ -x "$bin/lean" ]; then echo "$bin"; exit 0; fi
asset="lean-$num-linux.tar.zst"
url="https://github.com/leanprover/lean4/releases/download/$ver/$asset"
want="$(awk -F'|' -v u="$url" '$0 ~ u { gsub(/ /, "", $6); print $6 }' vendor/dmp/SETUP.md | head -1)"
mkdir -p "$dir"; cd "$dir"
if ! curl -sSfL -o "$asset" "$url" 2>/dev/null; then
  python3 - "$url" "$asset" <<'PY'
import os, ssl, sys, urllib.request, shutil
url, out = sys.argv[1], sys.argv[2]
ctx = ssl.create_default_context(cafile=os.environ.get("SSL_CERT_FILE", "/root/.ccr/ca-bundle.crt")) if os.path.exists(os.environ.get("SSL_CERT_FILE", "/root/.ccr/ca-bundle.crt")) else ssl.create_default_context()
handlers = [urllib.request.HTTPSHandler(context=ctx)]
if os.environ.get("HTTPS_PROXY"): handlers.insert(0, urllib.request.ProxyHandler({"https": os.environ["HTTPS_PROXY"]}))
with urllib.request.build_opener(*handlers).open(url, timeout=900) as r, open(out, "wb") as f: shutil.copyfileobj(r, f, 1 << 20)
PY
fi
got="$(sha256sum "$asset" | cut -d' ' -f1)"
if [ -n "$want" ] && [ "$got" != "$want" ]; then echo "FAIL $asset sha256 $got, the setup file says $want" >&2; exit 1; fi
if command -v zstd >/dev/null 2>&1; then zstd -dq "$asset" -o "${asset%.zst}" && tar -xf "${asset%.zst}" && rm -f "${asset%.zst}"
else python3 - "$asset" "$dir" <<'PY'
import sys, tarfile, zstandard
with open(sys.argv[1], "rb") as f, zstandard.ZstdDecompressor().stream_reader(f) as r, tarfile.open(fileobj=r, mode="r|") as t: t.extractall(sys.argv[2], filter="data")
PY
fi
rm -f "$asset"
[ -x "$bin/lean" ] || { echo "FAIL no lean at $bin" >&2; exit 1; }
echo "$bin"
