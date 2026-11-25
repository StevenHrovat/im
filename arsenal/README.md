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
| `Arsenal.Rotation` | The rotation API: a box with one command (the step at the one shared gate), its gate factor, a margin and a marker per step, `inside` or `r136a1`; the marker is correct when it agrees with the gate's own verdict, and DMP-complete means correct at every tick. The one-box certificate (one step at the shared gate certifies every tick), the scale certificate (every scale, from the sharing answered R136a1), the half-turn (the outside read through the same gate), a finite check, and the vacuity checks (a marker read off the gate always passes). |
| `Arsenal.Rigidity` | Rigidity as a one-box test: a manifold's presentations (its structure set) with the self-equivalences acting on them; the rigidity box is DMP-complete exactly when every presentation is the manifold seen through a self-equivalence (both directions); rigid from the shared gate (the sharing answered R136a1, never an axiom) and refuted by any non-rigid case; two presentations acting through a map to `ZMod 2` are rigid exactly when it is onto. |
| `Arsenal.GRH` | The generalized Riemann hypothesis, the claim of A. M. Masullo's draft *The Music of the Primes*, from Mathlib alone: GRH as a statement about an L-series' coefficients (every continuation off the pole at `1` has its strip zeros on the line; at most one continuation exists, so the statement does not depend on it); the zeta function and every Dirichlet L-function proved to be continuations; the Dedekind zeta function by its coefficients; the Hecke family as a supplied set of coefficient sequences that contains the Dirichlet characters (Mathlib v4.34.0 has no Hecke characters). The ladder Hecke, Dirichlet, Riemann is proved, ending in Mathlib's `RiemannHypothesis` (`riemannHypothesis_iff_onLine`). Masullo's route enters with its one open step, the gap (the exterior zeros of the trace formula cancel at every width), answered R136a1, and `masullo_gap_iff_grh` proves that open step equivalent to GRH itself. It proves nothing open. |
| `Arsenal.FullTurn` | The full turn: a quantity read off by going once around a point and averaging, the `+` half mirroring the `-` half. Discrete (`full_turn`, the `N`-th roots of unity summed over one turn; `full_turn_cos`; `full_turn_coeff`, coefficient extraction) and continuous (`full_turn_circle`, Cauchy's formula for the `n`-th Taylor coefficient; `full_turn_factorial`, `1 / n!` as one turn of `exp z / z ^ (n + 1)`; `full_turn_slope`, the `n`-th derivative as the ratio of two turns; `full_turn_leading` and `full_turn_order`, the leading coefficient and the order of a zero as one turn, for an L-function at `s = 1` the BSD leading coefficient and the analytic rank). The balance (`full_turn_balance`, `full_turn_balance_log`): a positive function on `N >= 2` points and its positive full-turn transform cannot both be flat, so some nontrivial free energy is at least `log (1 + √N)`; `N = 2` is the hand-over rate `log (1 + √2)`; `full_turn_balance_mean` gives the same for the mean over all nontrivial sectors of one type, a rate along a path that turns once through the sectors. Mathlib alone, nothing open. |
| `Arsenal.Observable` | The front door: every observable system (states, one step, its own decidable claim at each state) has a one-box description, a box of the rotation API whose marker is the claim and whose gate reads its truth. `box_complete_iff`: it is DMP-complete exactly when the claim holds at every tick (by construction, a restatement). `route`, `route_iff`: a route to the proof, the claim at the start and a step that keeps it. `route_everywhere`: once shown, certified at every tick and, with the gate shared across scales (answered `R136a1`), at every scale. `refuted_by_tick`: one failing tick refutes it. `ofReading`, `turn_gate`: a reading against a margin, and the gate read by one full turn when the reading is a coefficient hidden in a sum of `N` powers. Mathlib alone, nothing open. |

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
