/-
Birch and Swinnerton-Dyer: the Mathlib-only core, in native IM form.
Released under the Apache License 2.0.

First written for Gravity's YM work (the BSD instance of its problem API) and moved here as the first piece of the
arsenal; rederived here so that it carries nothing the old API needed and BSD does not. Imports Mathlib only.
-/

import Arsenal.BSD.Algebraic
import Arsenal.BSD.Analytic
import Arsenal.BSD.Count
import Arsenal.BSD.Hasse

/-!
# Birch and Swinnerton-Dyer: what can be proved from Mathlib alone

Both sides of BSD are derived from one Weierstrass equation `W` over a number field `K`: the rank of `E(K)` and the
order at `s = 1` of the L-function. This module states BSD as a property of `W` alone and proves what Mathlib gives
about it. Nothing here proves BSD or any part of it that is open.

* `Arsenal.BSD.Algebraic`: `E(K)`, Mordell-Weil from weak Mordell-Weil (the one part answered R136a1), finite torsion,
  the rank `algRank` in `ℕ∞` and "rank zero is finiteness", unconditionally.
* `Arsenal.BSD.Analytic`: the continuation, the order at `s = 1` well defined, parity from a local functional equation.
* `Arsenal.BSD.Count`: point counts over finite rings that run, proved equal to Mathlib's.
* `Arsenal.BSD.Hasse`: Hasse's bound, named (`Hasse`, answered R136a1), and what it gives: the local coefficient bounds,
  the first coefficient `1`, and a finite order at `s = 1` through one named Euler product step (`EulerProductBound`).
* Here: `BSDStatement W`, the existence line, the parity of the rank (with a finite rank from Hasse:
  `algRank_ne_top_of_hasse`, `rank_parity_of_hasse`), and the refined conjecture with every quantity Mathlib can
  derive derived.

## What was dropped, and why

The first form was shaped by Gravity's problem API (an input record with a curve, a conductor, an L-function and a root
number side by side). Against BSD itself:

* **Curves over `ℚ` only → any number field `K`.** Mathlib's heights, Northcott's property, descent and `W.LSeries` all
  hold over number fields; nothing used `ℚ`.
* **`algRank` as `Module.finrank` (junk `0` when `E(K)` is not finitely generated) → `Module.rank` in `ℕ∞`.** The true
  rank with no junk; it equals the `finrank` under Mordell-Weil (`algRank_eq_finrank`).
* **Finite generation as a hypothesis of "rank zero iff finite" and of the existence line → dropped.** Finite torsion
  suffices (`algRank_eq_zero_iff`, `existence_line`); weak Mordell-Weil is no longer needed anywhere but in
  `mordellWeil_of_weak`.
* **`IsContinuation`: an entire `Λ`, equal to the L-series on `re s > 3/2` → analytic on some half-plane `re s > a`,
  `a < 1`, equal to the series on some right half-plane.** BSD reads the germ at `s = 1` reached from the region of
  convergence; `3/2` is Hasse's bound, not in Mathlib. The old form still gives it (`IsContinuation.of_entire`), and the
  order stays well defined (`order_welldefined`).
* **`FunctionalEquation N Λ w` on the strip `0 < re s < 2`, with the conductor `N` free → near `s = 1`, with `A`
  existential and the degree `[K:ℚ]` from the field.** Parity reads only the germ at `1`, and the gamma factor and
  conductor only through "analytic and nonzero at `1`" (`order_parity_of_factor`). The old form gives the new
  (`FunctionalEquation.of_strip`). The root number `w` stays a name in the hypothesis but is never free in a conclusion:
  it is forced to be `(-1)^order` (`analytic_parity`).
* **`BSDStatement W Λ` (depending on a chosen `Λ`) → `BSDStatement W`**: a continuation exists and its order at `1` is the
  rank. With any continuation in hand it is that equation (`bsdStatement_iff`).
* **`RefinedBSD` with `r` and `tors` free → derived**: `r` is the rank, `tors` is `Nat.card` of the torsion, and the
  field's discriminant enters as `√|d_K|` (`1` over `ℚ`). Kept free, because Mathlib does not define them: the real period
  `Ω`, the regulator `Reg` (the canonical height is not in Mathlib, only the naive one), the order of the Tate-Shafarevich
  group `sha` (Galois cohomology of `E`), the product of the Tamagawa numbers `tam`.
* **`countZ`/`apZ`/`hasseZ` on five integers, inside a `noncomputable section` → `count`/`frobTrace`/`hasseCheck` on the
  curve itself over any finite ring**, with no `noncomputable section` anywhere: what runs is visibly computable.

Standard axioms only.
-/

namespace Arsenal.BSD

open Filter Topology

variable {K : Type*} [Field K] [DecidableEq K] [NumberField K]

/-- **The Birch and Swinnerton-Dyer conjecture** (rank part) for `W`: the L-series continues to `s = 1`, and the order of
its zero there is the rank of `E(K)`. A statement about `W` alone (the order does not depend on the continuation,
`order_welldefined`). Open in general. -/
def BSDStatement (W : WeierstrassCurve K) : Prop :=
  ∃ Λ : ℂ → ℂ, IsContinuation W Λ ∧ algRank W = analyticOrderAt Λ 1

/-- With a continuation in hand, BSD is the equation `rank = order of Λ at 1`. -/
theorem bsdStatement_iff {W : WeierstrassCurve K} {Λ : ℂ → ℂ} (hΛ : IsContinuation W Λ) :
    BSDStatement W ↔ algRank W = analyticOrderAt Λ 1 :=
  ⟨fun ⟨_, h', e⟩ => e.trans (order_welldefined h' hΛ), fun e => ⟨Λ, hΛ, e⟩⟩

/-- **The existence line**: under BSD, `E(K)` is infinite exactly when `L(E, 1) = 0`. Unconditional otherwise: no
finite generation is assumed. -/
theorem existence_line (W : WeierstrassCurve K) [W.IsElliptic] {Λ : ℂ → ℂ} (hΛ : IsContinuation W Λ)
    (h : BSDStatement W) : Infinite (Pts W) ↔ Λ 1 = 0 := by
  rw [infinite_iff_algRank_pos W, (bsdStatement_iff hΛ).1 h, zero_iff_order_ne_zero hΛ.analyticAt_one,
    pos_iff_ne_zero]

/-- **Parity of the rank under BSD**: with the functional equation, a finite rank `n` gives `w = (-1)^n`. -/
theorem rank_parity (W : WeierstrassCurve K) {Λ : ℂ → ℂ} (hΛ : IsContinuation W Λ) {w : ℂ}
    (hfe : FunctionalEquation K Λ w) (h : BSDStatement W) {n : ℕ} (hn : algRank W = n) : w = (-1) ^ n :=
  analytic_parity hΛ.analyticAt_one hfe (((bsdStatement_iff hΛ).1 h).symm.trans hn)

/-- **Parity of the rank under BSD and Mordell-Weil**: `w = (-1)^(finrank of E(K))`. -/
theorem rank_parity_of_fg (W : WeierstrassCurve K) (hfg : AddGroup.FG (Pts W)) {Λ : ℂ → ℂ}
    (hΛ : IsContinuation W Λ) {w : ℂ} (hfe : FunctionalEquation K Λ w) (h : BSDStatement W) :
    w = (-1) ^ Module.finrank ℤ (Pts W) :=
  rank_parity W hΛ hfe h (algRank_eq_finrank W hfg)

/-- **Under BSD and Hasse the rank is finite**: it is the order of a zero, which Hasse makes finite. -/
theorem algRank_ne_top_of_hasse (W : WeierstrassCurve K) {Λ : ℂ → ℂ} (hΛ : IsContinuation W Λ) (h : BSDStatement W)
    (hH : R136a1 "Hasse" (Hasse W)) (hE : R136a1 "Euler product bound" (EulerProductBound K)) : algRank W ≠ ⊤ := by
  rw [(bsdStatement_iff hΛ).1 h]
  exact order_ne_top hΛ hH hE

/-- **Parity of the rank under BSD and Hasse**, with no rank given separately: `w = (-1)^rank`. -/
theorem rank_parity_of_hasse (W : WeierstrassCurve K) {Λ : ℂ → ℂ} (hΛ : IsContinuation W Λ) {w : ℂ}
    (hfe : FunctionalEquation K Λ w) (h : BSDStatement W) (hH : R136a1 "Hasse" (Hasse W))
    (hE : R136a1 "Euler product bound" (EulerProductBound K)) : w = (-1) ^ (algRank W).toNat :=
  rank_parity W hΛ hfe h (ENat.natCast_toNat (algRank_ne_top_of_hasse W hΛ h hH hE)).symm

/-- **The refined conjecture** (leading coefficient). Derived from `W`: the rank `r`, the order of the torsion, the
discriminant `d_K` of the field. Named, because Mathlib does not define them: the real period `Ω`, the regulator `Reg`,
the order of the Tate-Shafarevich group `sha`, the product of the Tamagawa numbers `tam`. Near `s = 1`,
`Λ s = (s - 1)^r g s` with `g 1 = Ω Reg sha tam / (#tors² √|d_K|)`. -/
def RefinedBSD (W : WeierstrassCurve K) (Ω Reg : ℝ) (sha tam : ℕ) : Prop :=
  ∃ Λ : ℂ → ℂ, IsContinuation W Λ ∧ ∃ r : ℕ, algRank W = r ∧ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧
    (∀ᶠ s in 𝓝 (1 : ℂ), Λ s = (s - 1) ^ r * g s) ∧
    g 1 = ((Ω * Reg * sha * tam /
      ((Nat.card (AddCommGroup.torsion (Pts W)) : ℝ) ^ 2 * Real.sqrt |(NumberField.discr K : ℝ)|) : ℝ) : ℂ)

/-- **The refined conjecture gives the rank statement** when its leading coefficient is nonzero (the torsion and the
discriminant never vanish). -/
theorem bsd_of_refined (W : WeierstrassCurve K) [W.IsElliptic] {Ω Reg : ℝ} {sha tam : ℕ}
    (h : RefinedBSD W Ω Reg sha tam) (hne : Ω * Reg * sha * tam ≠ 0) : BSDStatement W := by
  obtain ⟨Λ, hΛ, r, hr, g, hg, hev, hg1⟩ := h
  have := torsion_finite W
  have htors : (Nat.card (AddCommGroup.torsion (Pts W)) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hdisc : Real.sqrt |(NumberField.discr K : ℝ)| ≠ 0 :=
    Real.sqrt_ne_zero'.2 (abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero K)))
  refine ⟨Λ, hΛ, hr.trans ((hΛ.analyticAt_one.analyticOrderAt_eq_natCast).2 ⟨g, hg, ?_, ?_⟩).symm⟩
  · rw [hg1]
    exact Complex.ofReal_ne_zero.2 (div_ne_zero hne (mul_ne_zero (pow_ne_zero _ htors) hdisc))
  · filter_upwards [hev] with s hs
    rw [hs, smul_eq_mul]

end Arsenal.BSD
