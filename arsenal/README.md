# The arsenal

IM's growing set of transferable Lean results that need Mathlib: content-free pieces that more than one project uses, kept once, here,
and imported from here only (never copied). Lean v4.34.0 and Mathlib v4.34.0, nothing else. The rest of IM (`proof/`) stays
Mathlib-free.

| Module | What it is |
|---|---|
| `Arsenal.R136a1` | The one way to leave a statement open: `R136a1 "name" P`, a named hypothesis, never an axiom (DMP chapters 01 and 06). |
| `Arsenal.BSD` | Birch and Swinnerton-Dyer, what Mathlib alone gives: Mordell-Weil from weak Mordell-Weil, finite torsion, the analytic rank well defined, its parity from the functional equation, the existence line (`E(Q)` infinite exactly when `L(E, 1) = 0`, under BSD), point counts mod `p` that run and equal Mathlib's. It proves nothing open. |

## The gate

Every change shows one thing: it contains nothing that cannot run, so nothing that cannot be soundly constructed.

```
arsenal/tools/lint.sh            # static, no network: Mathlib v4.34.0 only, no escape hatch, every module reached; lists the R136a1 parts
arsenal/tools/lint-selftest.sh   # each lint rule fails on a planted case (named R136a1) and prose passes
arsenal/tools/check.sh           # the full check: lint, build against Mathlib (about 5 GB), the kernel's axiom report for every declaration
```

`tools/verify` (IM's one gate) runs the lint and its self-test. The full check needs Mathlib's prebuilt files, so it runs where the arsenal
is used: Gravity's builds import it and audit every declaration they depend on.

## Using it

In a Lake project on Lean v4.34.0 with Mathlib v4.34.0:

```toml
[[require]]
name = "arsenal"
git = "https://github.com/StevenHrovat/im"
rev = "<commit>"
subDir = "arsenal"
```

then `import Arsenal.BSD` (or `import Arsenal`).

Mathlib (Apache License 2.0) is the ground all of this stands on; `Arsenal.BSD` uses its Weierstrass curves, the group law, the naive
height and descent, and the L-function of a Weierstrass curve. Thanks to its authors.

Licensed under the Apache License 2.0 (`../LICENSE`).
