# The arsenal

IM's growing set of transferable Lean results that need Mathlib: content-free pieces that more than one project uses, kept once, here,
and imported from here only (never copied). Lean v4.34.0 and Mathlib v4.34.0, nothing else. The rest of IM (`proof/`) stays
Mathlib-free.

| Module | What it is |
|---|---|
| `Arsenal.R136a1` | The one way to leave a statement open: `R136a1 "name" P`, a named hypothesis, never an axiom (DMP chapters 01 and 06). |
| `Arsenal.BSD` | Birch and Swinnerton-Dyer, what Mathlib alone gives, over any number field: `BSDStatement W`, a statement about the curve alone; the existence line (`E(K)` infinite exactly when `L(E, 1) = 0`, under BSD, with no finite generation assumed); the parity of the rank; the refined conjecture with every quantity Mathlib can derive derived. It proves nothing open. The module docstring lists what the first form carried that BSD does not need. |
| `Arsenal.BSD.Algebraic` | `E(K)`, Mordell-Weil from weak Mordell-Weil (answered R136a1), finite torsion, the rank in `ℕ∞` (no junk value), rank zero exactly when `E(K)` is finite. |
| `Arsenal.BSD.Analytic` | The continuation (analytic on a half-plane containing `s = 1`), the order at `s = 1` well defined, parity from a functional equation near `s = 1`. |
| `Arsenal.BSD.Count` | Point counts over any finite ring, computable and checked by the kernel, proved equal to Mathlib's count over finite fields. |
| `Arsenal.BSD.Hasse` | Hasse's bound, named (answered R136a1), and what it gives: the local coefficient bounds of Mathlib's `W.LFunction`, its first coefficient `1`, and a finite order of the zero at `s = 1` through one named Euler product step. |
| `Arsenal.BSD.EulerRat` | The Euler product bound over `ℚ`, proved (`eulerProductBound_rat`): products with Hasse-type coefficient bounds converge absolutely for `re s > 3/2`, dominated by `ζ(s - 1/2)^2`. So over `ℚ` only Hasse stays named, and the finite order at `s = 1` and parity follow from it alone. |

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
