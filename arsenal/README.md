# The arsenal

IM's growing set of transferable Lean results that need Mathlib: content-free pieces that more than one project uses, kept once, here,
and imported from here only (never copied). Lean v4.34.0 and Mathlib v4.34.0, nothing else. The rest of IM (`proof/`) stays
Mathlib-free.

**The core (`arsenal/core`)**: the verify toy's finite layer, a package of its own with no requirement at all, not even Mathlib
(`ArsenalCore.Toy`: the string `vxunderground`, smelly, Moin as the leading zero, and that a bit rotation is never smelly;
`ArsenalCore.Matrix`: the explanation mechanism, k by k tables of proofs, their extension, derivation and the DAG of versions;
`ArsenalCore.Optimizer`: its mirror, the transitive reduction of a DAG, which keeps every derivation and is the only settled form;
`ArsenalCore.Possibility`: the right angle, the sector map and the two answers of a yes/no question). The facts
about bytes and the string are decided by the kernel's evaluation; the general facts about `n`-bit words are proved from Lean's core
lemmas on natural numbers; most rest on no axiom at all. It builds in seconds with nothing to download, so `tools/verify`, and with it
the verify workflow, builds and audits it on every change (`arsenal/core/tools/check.sh`). Lean need not trust a library: every Mathlib proof is a term that a small kernel can check again (the de Bruijn
criterion). Mathlib's own build does; prebuilt files fetched by `lake exe cache get` are loaded without a new check, and a
replay (Lean's `lean4checker`, or a second kernel such as nanoda over `lean4export`) repeats the check locally. What is trusted
is the kernel, with its built-in arithmetic on natural numbers, Lean's prelude definitions and the axioms the report lists. What the arsenal takes
from Mathlib is its definitions of infinite objects (the complex numbers, the circle, the integral), which no evaluation can establish
and which are read, not computed; that layer imports Mathlib as an API.

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
| `Arsenal.RHLibrary` | The Lean proof of the Riemann hypothesis (`leanprover-community/riemann-hypothesis`, Levent Alpoge's proof, read at commit `de330e7`) merged in, not imported: its Mathlib-only statement file copied word for word, its five theorems as one input answered R136a1 (the library is on Lean v4.37.0-rc1 and a later Mathlib, so the arsenal matches the text, not the check). Proved here: the zeta statement is Mathlib's `RiemannHypothesis`, its GRH is `Arsenal.GRH.DirichletGRH` at every modulus, and the five are one statement (`library_iff`, theorem 4 alone gives the other four, theorem 1 through this arsenal's own ladder). From the input: GRH for every Dirichlet L-series and for zeta in coefficient form, Masullo's gap at every width for Dirichlet L-functions (the Hecke and Dedekind cases stay open), and the moduli as an observable system whose one-box description is DMP-complete exactly when the input holds (`moduli_complete_iff_input`). |
| `Arsenal.Problems` | The translation layer: every problem as one card (a name and its statement) of the one-box API, all on one gate. A card's one-box description is DMP-complete exactly when its statement holds (`Card.complete_iff`), so the translation carries each problem whole into its one open step and decides none; an outside proof enters answered R136a1 (`Card.certified`). The seven Millennium Prize problems as one layer (`millennium`): the Riemann hypothesis (Mathlib's statement, answered by `Arsenal.RHLibrary`), Poincaré (stated from Mathlib's manifolds, answered by Perelman's proof as R136a1), P ≠ NP (stated from Mathlib's polynomial-time Turing machines), BSD over `ℚ` (`Arsenal.BSD`), and Navier-Stokes, Yang-Mills and Hodge as supplied statements (Mathlib v4.34.0 cannot write them). `millennium_left`: with the two outside inputs, the layer is DMP-complete exactly when the five remaining statements hold. The paper it serves: [Draft 6 of GUID v8](https://github.com/StevenHrovat/gravity/blob/main/docs/paper/D6/latex/guid-v8-D6.pdf). |
| `Arsenal.FullTurn` | The full turn: a quantity read off by going once around a point and averaging, the `+` half mirroring the `-` half. Discrete (`full_turn`, the `N`-th roots of unity summed over one turn; `full_turn_cos`; `full_turn_coeff`, coefficient extraction) and continuous (`full_turn_circle`, Cauchy's formula for the `n`-th Taylor coefficient; `full_turn_factorial`, `1 / n!` as one turn of `exp z / z ^ (n + 1)`; `full_turn_slope`, the `n`-th derivative as the ratio of two turns; `full_turn_leading` and `full_turn_order`, the leading coefficient and the order of a zero as one turn, for an L-function at `s = 1` the BSD leading coefficient and the analytic rank). The balance (`full_turn_balance`, `full_turn_balance_log`): a positive function on `N >= 2` points and its positive full-turn transform cannot both be flat, so some nontrivial free energy is at least `log (1 + √N)`; `N = 2` is the hand-over rate `log (1 + √2)`; `full_turn_balance_mean` gives the same for the mean over all nontrivial sectors of one type, a rate along a path that turns once through the sectors. Mathlib alone, nothing open. |
| `Arsenal.Observable` | The front door: every observable system (states, one step, its own decidable claim at each state) has a one-box description, a box of the rotation API whose marker is the claim and whose gate reads its truth. `box_complete_iff`: it is DMP-complete exactly when the claim holds at every tick (by construction, a restatement). `route`, `route_iff`: a route to the proof, the claim at the start and a step that keeps it. `route_everywhere`: once shown, certified at every tick and, with the gate shared across scales (answered `R136a1`), at every scale. `refuted_by_tick`: one failing tick refutes it. `prod`, `route_prod`: reassembly, two routes give a route for the pair. `ofReading`, `turn_gate`: a reading against a margin, and the gate read by one full turn when the reading is a coefficient hidden in a sum of `N` powers. Mathlib alone, nothing open. |
| `Arsenal.Toy` | The verify toy, on binary words. `evens k` (k-bit words stepping by two, claim even): the route shown, the step checked on a byte by one kernel evaluation, and every bit width sharing the gate with one bit by reduction modulo 2, so the sharing across scales is proved and the route certifies every width (`evens_everywhere`). `counter k` (stepping by one): the gate says R136a1 at tick 1 and the box is refuted (`counter_gate`, `counter_refuted`). `pair_route`: two routes reassembled into one by `Observable.route_prod`. The string `vxunderground` in binary (`vx_binary`), certified byte by byte (`vxRead_complete`), hidden by a half-turn of the alphabet (`vx_rot13`, `ikhaqretebhaq`) and returned by completing the full turn (`vx_rot13_twice`); a state whose turn does not complete is smelly, exactly when the two rotations do not add up to a multiple of 26 (`Smelly`, `smelly_iff_not_full`). The leading zero: rotating an n-bit word left is an exact doubling exactly when its leading bit is 0 (`rotl_eq_double_iff`), and every byte of the string has one, so its rotation doubles every byte (`vx_rotl`). |
| `Arsenal.Decode` | Encoding, decoding, and smelly states: a state is smelly when decoding its encoding does not return it. `never_smelly_iff` (never smelly is a left inverse), `exists_clean_decoder` (an injective encoding has a decoder never smelly), `smelly_of_not_injective` (a lossy encoding makes every decoder smelly somewhere), `hash_smelly` (every hash does), `turn_decodes` (the full turn decodes every one of its N coefficients), `toy_smelly_iff` (the toy's smelly states are this notion). Mathlib alone, nothing open. |

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
