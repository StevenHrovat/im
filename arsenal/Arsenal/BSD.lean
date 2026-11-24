/-
Birch and Swinnerton-Dyer: the Mathlib-only core.
Released under the Apache License 2.0.

Written for Gravity's YM work (the BSD instance of its problem API, which imports this module) and moved here as the first
piece of the arsenal. Imports Mathlib only.
-/

import Mathlib

/-!
# Birch and Swinnerton-Dyer: what can be proved from Mathlib alone

This file imports only Mathlib (v4.34.0). It supplies the pieces the BSD instance needs that Mathlib does not state, each
proved from what Mathlib has. Nothing here proves BSD or any part of it that is open.

* **Mordell-Weil from weak Mordell-Weil** (`mordellWeil_of_weak`): Mathlib has the naive height on an elliptic curve, its
  approximate parallelogram law, Northcott's property over number fields and the descent theorem; so the one missing
  input is the finiteness of `E(ℚ)/2E(ℚ)`. With it, `E(ℚ)` is finitely generated. The torsion part is finite
  unconditionally (`torsion_finite`, Mathlib's `finite_torsion`).
* **The two counts.** The algebraic rank (`algRank`, the rank of `E(ℚ)` as a `ℤ`-module) and the analytic rank (the order
  of the zero at `s = 1` of an entire continuation of Mathlib's L-series, `analyticOrderAt Λ 1`). The continuation is not
  in Mathlib (it is modularity); here it is a hypothesis (`IsContinuation`), and the analytic rank does not depend on which
  continuation is taken (`continuation_unique`, `order_welldefined`).
* **Parity from the functional equation** (`order_parity`, `analytic_parity`): if the completed function
  `ξ = gammaFactor N · Λ` satisfies `ξ (2 - s) = w ξ s` near `s = 1`, the order of the zero of `Λ` at `1` is even when
  `w = 1` and odd when `w = -1` (the gamma factor is analytic and nonzero at `1`, `completed_order`).
* **The existence line** (`existence_line`): given finite generation and BSD, `E(ℚ)` is infinite exactly when `L(E, 1) = 0`.
* **Point counts that run** (`countZ`, `apZ`, `count_correct`): the number of points mod `p`, computed on integer
  coefficients, is Mathlib's `Nat.card` of the reduced curve's points at every good prime; the Hasse check `hasseZ` is
  decidable and is the real Hasse inequality (`hasseZ_iff`).

Standard axioms only.
-/

noncomputable section

namespace Arsenal.BSD

open WeierstrassCurve Filter Topology

/-! ## 1. Mordell-Weil from weak Mordell-Weil; finite torsion -/

/-- The group `E(K)` of a Weierstrass curve over a field (Mathlib's nonsingular affine points with the point at infinity,
with the chord-tangent law). -/
abbrev Pts {K : Type*} [Field K] (W : WeierstrassCurve K) : Type _ := W.toAffine.Point

/-- **Weak Mordell-Weil** (the named statement): `2 E(ℚ)` has finite index in `E(ℚ)`, i.e. `E(ℚ)/2E(ℚ)` is finite.
Classical (Mordell 1922; the proof uses the finiteness of class groups and unit groups); not in Mathlib. -/
def WeakMordellWeil (W : WeierstrassCurve ℚ) : Prop :=
  (nsmulAddMonoidHom (α := Pts W) 2).range.FiniteIndex

/-- **Mordell-Weil from weak Mordell-Weil**: if `E(ℚ)/2E(ℚ)` is finite, `E(ℚ)` is finitely generated. The proof is
Mathlib's descent theorem with the naive height: it is nonnegative, satisfies the approximate parallelogram law, and has
Northcott's property over `ℚ`. -/
theorem mordellWeil_of_weak (W : WeierstrassCurve ℚ) [W.IsElliptic] (h : WeakMordellWeil W) : AddGroup.FG (Pts W) := by
  obtain ⟨C, hC⟩ := WeierstrassCurve.Affine.approx_parallelogram_law (W := W.toAffine)
  exact AddCommGroup.fg_of_descent' (h := WeierstrassCurve.Affine.Point.naiveHeight) h
    (fun P => by rw [WeierstrassCurve.Affine.Point.naiveHeight_eq_logHeight]; exact Height.logHeight_nonneg _) hC

/-- **The torsion of `E(ℚ)` is finite**, unconditionally (Mathlib's `finite_torsion`, from the same height). -/
theorem torsion_finite (W : WeierstrassCurve ℚ) [W.IsElliptic] : Finite (AddCommGroup.torsion (Pts W)) :=
  WeierstrassCurve.Affine.finite_torsion (W := W.toAffine)

/-! ## 2. The algebraic rank and the existence of points of infinite order -/

/-- **The algebraic rank** of `E(ℚ)`: its rank as a `ℤ`-module (the number of independent points of infinite order).
It is the true rank when `E(ℚ)` is finitely generated (Mordell-Weil); otherwise Mathlib's `finrank` is a junk `0`. -/
def algRank (W : WeierstrassCurve ℚ) : ℕ := Module.finrank ℤ (Pts W)

/-- **Rank zero is finiteness**: for a finitely generated `E(ℚ)`, the rank is zero exactly when `E(ℚ)` is finite (every
point is then torsion, and the torsion is finite). -/
theorem algRank_eq_zero_iff (W : WeierstrassCurve ℚ) [W.IsElliptic] (hfg : AddGroup.FG (Pts W)) :
    algRank W = 0 ↔ Finite (Pts W) := by
  have : Module.Finite ℤ (Pts W) := Module.Finite.iff_addGroup_fg.2 hfg
  unfold algRank
  rw [Module.finrank_eq_zero_iff]
  constructor
  · intro h
    have hT : ∀ x : Pts W, x ∈ AddCommGroup.torsion (Pts W) := fun x => by
      obtain ⟨a, ha, hax⟩ := h x
      exact (isOfFinAddOrder_iff_zsmul_eq_zero).2 ⟨a, ha, hax⟩
    have := torsion_finite W
    exact Finite.of_injective (fun x => (⟨x, hT x⟩ : AddCommGroup.torsion (Pts W)))
      (fun x y hxy => congrArg Subtype.val hxy)
  · intro hfin x
    refine ⟨(addOrderOf x : ℤ), ?_, ?_⟩
    · exact_mod_cast (addOrderOf_pos x).ne'
    · rw [natCast_zsmul, addOrderOf_nsmul_eq_zero]

/-- **Points of infinite order exist exactly when the rank is positive** (finitely generated `E(ℚ)`). -/
theorem infinite_iff_algRank_pos (W : WeierstrassCurve ℚ) [W.IsElliptic] (hfg : AddGroup.FG (Pts W)) :
    Infinite (Pts W) ↔ 0 < algRank W := by
  rw [Nat.pos_iff_ne_zero, Ne, algRank_eq_zero_iff W hfg, not_finite_iff_infinite]

/-! ## 3. The analytic rank: the order of the zero at `s = 1` -/

/-- **An entire continuation of the L-series** (Mathlib's `W.LSeries`, the Dirichlet series of the Euler product, which
converges for `re s > 3/2`): an entire function equal to it there. Its existence is modularity (Wiles, Taylor-Wiles,
Breuil-Conrad-Diamond-Taylor); not in Mathlib. -/
def IsContinuation (W : WeierstrassCurve ℚ) (Λ : ℂ → ℂ) : Prop :=
  Differentiable ℂ Λ ∧ ∀ s : ℂ, 3 / 2 < s.re → Λ s = W.LSeries s

/-- **The continuation is unique**: two entire functions equal to the L-series on `re s > 3/2` are equal (the identity
theorem). -/
theorem continuation_unique {W : WeierstrassCurve ℚ} {Λ₁ Λ₂ : ℂ → ℂ} (h₁ : IsContinuation W Λ₁)
    (h₂ : IsContinuation W Λ₂) : Λ₁ = Λ₂ := by
  have hU : {s : ℂ | 3 / 2 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  refine AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ) (z₀ := 2) (fun z _ => h₁.1.analyticAt z)
    (fun z _ => h₂.1.analyticAt z) ?_
  filter_upwards [hU] with s hs
  rw [h₁.2 s hs, h₂.2 s hs]

/-- **The analytic rank is well defined**: every continuation has the same order of zero at `s = 1`. -/
theorem order_welldefined {W : WeierstrassCurve ℚ} {Λ₁ Λ₂ : ℂ → ℂ} (h₁ : IsContinuation W Λ₁)
    (h₂ : IsContinuation W Λ₂) : analyticOrderAt Λ₁ 1 = analyticOrderAt Λ₂ 1 := by
  rw [continuation_unique h₁ h₂]

/-- **The zero at `s = 1` exists exactly when the order is positive** (for an entire function). -/
theorem zero_iff_order_ne_zero {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ) :
    Λ 1 = 0 ↔ analyticOrderAt Λ 1 ≠ 0 := by
  rw [analyticOrderAt_ne_zero]
  exact ⟨fun h => ⟨hΛ.analyticAt 1, h⟩, fun h => h.2⟩

/-- **Parity from the functional equation.** If `Λ` is analytic at `1`, `Λ (2 - s) = w Λ s` near `s = 1`, and the order
of the zero at `1` is a natural number `n`, then `w = (-1)^n`. -/
theorem order_parity {Λ : ℂ → ℂ} (hΛ : AnalyticAt ℂ Λ 1) {w : ℂ} (hfe : ∀ᶠ s in 𝓝 (1 : ℂ), Λ (2 - s) = w * Λ s)
    {n : ℕ} (hn : analyticOrderAt Λ 1 = n) : w = (-1) ^ n := by
  obtain ⟨g, hg, hg1, hev⟩ := (hΛ.analyticOrderAt_eq_natCast).1 hn
  have hτ : Tendsto (fun s : ℂ => 2 - s) (𝓝 1) (𝓝 1) := by
    have : Continuous (fun s : ℂ => 2 - s) := continuous_const.sub continuous_id
    have h := this.tendsto 1
    rwa [show (2 : ℂ) - 1 = 1 by norm_num] at h
  have hev' := hτ.eventually hev
  -- on a punctured neighbourhood of `1`, `(-1)^n g (2 - s) = w g s`
  have hpunct : ∀ᶠ s in 𝓝[≠] (1 : ℂ), (-1) ^ n * g (2 - s) = w * g s := by
    filter_upwards [nhdsWithin_le_nhds hev, nhdsWithin_le_nhds hev', nhdsWithin_le_nhds hfe, self_mem_nhdsWithin]
      with s h1 h2 h3 hs
    have hs' : (s - 1) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hs)
    have key : (s - 1) ^ n * ((-1) ^ n * g (2 - s)) = (s - 1) ^ n * (w * g s) := by
      have e1 : Λ (2 - s) = (s - 1) ^ n * ((-1) ^ n * g (2 - s)) := by
        rw [h2, smul_eq_mul, show (2 - s - 1) = (-1) * (s - 1) by ring, mul_pow]; ring
      have e2 : w * Λ s = (s - 1) ^ n * (w * g s) := by rw [h1, smul_eq_mul]; ring
      rw [← e1, ← e2, h3]
    exact mul_left_cancel₀ hs' key
  have hgc : ContinuousAt g 1 := hg.continuousAt
  have hL : Tendsto (fun s => (-1) ^ n * g (2 - s)) (𝓝[≠] (1 : ℂ)) (𝓝 ((-1) ^ n * g 1)) :=
    ((hgc.tendsto.comp hτ).const_mul _).mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun s => w * g s) (𝓝[≠] (1 : ℂ)) (𝓝 (w * g 1)) :=
    (hgc.tendsto.const_mul _).mono_left nhdsWithin_le_nhds
  have heq : (-1) ^ n * g 1 = w * g 1 := tendsto_nhds_unique (hL.congr' hpunct) hR
  exact (mul_right_cancel₀ hg1 heq).symm

/-- **The gamma factor** of an elliptic curve of conductor `N`: `N^{s/2} (2π)^{-s} Γ(s)`. The completed L-function is
`ξ s = gammaFactor N s · L(E, s)`; its functional equation is `ξ (2 - s) = w ξ s` with the root number `w = ±1`. -/
def gammaFactor (N : ℕ) (s : ℂ) : ℂ := (N : ℂ) ^ (s / 2) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s

/-- The gamma factor is analytic at `s = 1`. -/
theorem gammaFactor_analyticAt {N : ℕ} (hN : 0 < N) : AnalyticAt ℂ (gammaFactor N) 1 := by
  have hU : {s : ℂ | 0 < s.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  refine DifferentiableOn.analyticAt (fun s hs => ?_) hU
  have hs' : ∀ m : ℕ, s ≠ -m := fun m h => by
    have : (0 : ℝ) < (-(m : ℂ)).re := h ▸ hs
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  exact ((((differentiableAt_id.div_const 2).const_cpow (Or.inl hN')).mul
    (differentiableAt_id.neg.const_cpow (Or.inl h2π))).mul (Complex.differentiableAt_Gamma s hs')).differentiableWithinAt

/-- The gamma factor does not vanish at `s = 1`. -/
theorem gammaFactor_one_ne_zero {N : ℕ} (hN : 0 < N) : gammaFactor N 1 ≠ 0 := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  unfold gammaFactor
  rw [Complex.Gamma_one, mul_one]
  exact mul_ne_zero (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num) |>.2 hN')
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num) |>.2 h2π)

/-- **The completed function has the same order at `s = 1`** as the L-function (the gamma factor is analytic and nonzero
there). -/
theorem completed_order {N : ℕ} (hN : 0 < N) {Λ : ℂ → ℂ} (hΛ : AnalyticAt ℂ Λ 1) :
    analyticOrderAt (fun s => gammaFactor N s * Λ s) 1 = analyticOrderAt Λ 1 := by
  have h0 : analyticOrderAt (gammaFactor N) 1 = 0 :=
    analyticOrderAt_eq_zero.2 (Or.inr (gammaFactor_one_ne_zero hN))
  have := analyticOrderAt_mul (gammaFactor_analyticAt hN) hΛ
  rw [h0, zero_add] at this
  exact this

/-- **The functional equation** of the completed L-function, on the critical strip `0 < re s < 2` (where the gamma factor
has no pole): `ξ (2 - s) = w ξ s`. Its proof is modularity; not in Mathlib. -/
def FunctionalEquation (N : ℕ) (Λ : ℂ → ℂ) (w : ℂ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 2 → gammaFactor N (2 - s) * Λ (2 - s) = w * (gammaFactor N s * Λ s)

/-- **Parity of the analytic rank** (unconditional, from the functional equation): `w = (-1)^(order of L(E, s) at 1)`. -/
theorem analytic_parity {N : ℕ} (hN : 0 < N) {Λ : ℂ → ℂ} (hΛ : AnalyticAt ℂ Λ 1) {w : ℂ}
    (hfe : FunctionalEquation N Λ w) {n : ℕ} (hn : analyticOrderAt Λ 1 = n) : w = (-1) ^ n := by
  have hU : {s : ℂ | 0 < s.re ∧ s.re < 2} ∈ 𝓝 (1 : ℂ) :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds (by norm_num)
  refine order_parity ((gammaFactor_analyticAt hN).mul hΛ) ?_ ((completed_order hN hΛ).trans hn)
  filter_upwards [hU] with s hs
  exact hfe s hs.1 hs.2

/-! ## 4. The statement and the existence line -/

/-- **The Birch and Swinnerton-Dyer conjecture** (rank part) for a curve `W` and a continuation `Λ` of its L-series:
the algebraic rank equals the order of the zero of `Λ` at `s = 1`. Open in general. -/
def BSDStatement (W : WeierstrassCurve ℚ) (Λ : ℂ → ℂ) : Prop := ((algRank W : ℕ) : ℕ∞) = analyticOrderAt Λ 1

/-- **The existence line**: for a finitely generated `E(ℚ)` and an entire `Λ`, BSD gives "`E(ℚ)` is infinite exactly
when `Λ (1) = 0`": the zero at `s = 1` exists exactly when a point of infinite order exists. -/
theorem existence_line (W : WeierstrassCurve ℚ) [W.IsElliptic] (hfg : AddGroup.FG (Pts W)) {Λ : ℂ → ℂ}
    (hΛ : Differentiable ℂ Λ) (h : BSDStatement W Λ) : Infinite (Pts W) ↔ Λ 1 = 0 := by
  rw [infinite_iff_algRank_pos W hfg, zero_iff_order_ne_zero hΛ, ← h, Nat.pos_iff_ne_zero, Ne, Ne,
    Nat.cast_eq_zero]

/-- **Parity of the rank under BSD**: with the functional equation of the completed function, BSD gives
`w = (-1)^rank`. -/
theorem rank_parity (W : WeierstrassCurve ℚ) {N : ℕ} (hN : 0 < N) {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ) {w : ℂ}
    (hfe : FunctionalEquation N Λ w) (h : BSDStatement W Λ) : w = (-1) ^ algRank W :=
  analytic_parity hN (hΛ.analyticAt 1) hfe h.symm

/-- **The refined conjecture** (leading coefficient), on named quantities that Mathlib does not define: the real period
`Ω`, the regulator `Reg` (from the canonical height), the order of the Tate-Shafarevich group `sha`, the product of the
Tamagawa numbers `tam`, the order of the torsion `tors`. Near `s = 1`, `Λ s = (s - 1)^r g s` with
`g 1 = Ω Reg sha tam / tors²`. -/
def RefinedBSD (Λ : ℂ → ℂ) (r : ℕ) (Ω Reg : ℝ) (sha tam tors : ℕ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ (∀ᶠ s in 𝓝 (1 : ℂ), Λ s = (s - 1) ^ r * g s) ∧
    g 1 = ((Ω * Reg * sha * tam / (tors : ℝ) ^ 2 : ℝ) : ℂ)

/-- The refined conjecture with a nonzero leading coefficient contains the rank statement's analytic side: the order of
the zero is exactly `r`. -/
theorem order_of_refined {Λ : ℂ → ℂ} {r : ℕ} {Ω Reg : ℝ} {sha tam tors : ℕ} (hΛ : Differentiable ℂ Λ)
    (h : RefinedBSD Λ r Ω Reg sha tam tors) (hne : Ω * Reg * sha * tam / (tors : ℝ) ^ 2 ≠ 0) :
    analyticOrderAt Λ 1 = r := by
  obtain ⟨g, hg, hev, hg1⟩ := h
  refine ((hΛ.analyticAt 1).analyticOrderAt_eq_natCast).2 ⟨g, hg, ?_, ?_⟩
  · rw [hg1]; exact_mod_cast hne
  · filter_upwards [hev] with s hs
    rw [hs, smul_eq_mul]

/-! ## 5. Points mod `p`: a count that runs, proved equal to Mathlib's -/

/-- **The number of points mod `p`**, computed from integer coefficients: the affine solutions over `ZMod p`, plus the
point at infinity. -/
def countZ (a₁ a₂ a₃ a₄ a₆ : ℤ) (p : ℕ) [NeZero p] : ℕ :=
  (Finset.univ.filter fun xy : ZMod p × ZMod p =>
    xy.2 ^ 2 + (a₁ : ZMod p) * xy.1 * xy.2 + (a₃ : ZMod p) * xy.2 =
      xy.1 ^ 3 + (a₂ : ZMod p) * xy.1 ^ 2 + (a₄ : ZMod p) * xy.1 + (a₆ : ZMod p)).card + 1

/-- **The trace of Frobenius** `a_p = p + 1 - #E(F_p)`, computed. -/
def apZ (a₁ a₂ a₃ a₄ a₆ : ℤ) (p : ℕ) [NeZero p] : ℤ := (p : ℤ) + 1 - countZ a₁ a₂ a₃ a₄ a₆ p

/-- **The Hasse check**, decidable: `a_p^2 ≤ 4 p`. -/
def hasseZ (a₁ a₂ a₃ a₄ a₆ : ℤ) (p : ℕ) [NeZero p] : Bool := decide (apZ a₁ a₂ a₃ a₄ a₆ p ^ 2 ≤ 4 * p)

/-- **The check is the real Hasse inequality** `|a_p| ≤ 2 √p`. -/
theorem hasseZ_iff (a₁ a₂ a₃ a₄ a₆ : ℤ) (p : ℕ) [NeZero p] :
    hasseZ a₁ a₂ a₃ a₄ a₆ p = true ↔ |(apZ a₁ a₂ a₃ a₄ a₆ p : ℝ)| ≤ 2 * Real.sqrt p := by
  unfold hasseZ
  rw [decide_eq_true_iff]
  set a := apZ a₁ a₂ a₃ a₄ a₆ p
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have h2 : (2 * Real.sqrt p) ^ 2 = 4 * p := by rw [mul_pow, Real.sq_sqrt hp]; norm_num
  have habs : |2 * Real.sqrt p| = 2 * Real.sqrt p := abs_of_nonneg (by positivity)
  have hcast : (a ^ 2 ≤ 4 * (p : ℤ)) ↔ ((a : ℝ)) ^ 2 ≤ 4 * (p : ℝ) := by
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  rw [hcast, ← h2, sq_le_sq, habs]

/-- **The computed count is Mathlib's.** For an integral Weierstrass curve `W` and a prime `p` of good reduction
(`Δ ≠ 0` mod `p`), the number of points of the reduced curve over `ZMod p` (Mathlib's `Nat.card` of its group) is
`countZ`. -/
theorem count_correct (W : WeierstrassCurve ℤ) (p : ℕ) [hp : Fact p.Prime] (hΔ : ((W.Δ : ℤ) : ZMod p) ≠ 0) :
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    Nat.card (Pts (W.map (Int.castRingHom (ZMod p)))) = countZ W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ p := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  set Wp := W.map (Int.castRingHom (ZMod p))
  have : Wp.IsElliptic := ⟨by rw [map_Δ]; exact isUnit_iff_ne_zero.2 hΔ⟩
  rw [Nat.card_congr (WeierstrassCurve.Affine.pointEquiv Wp.toAffine)]
  have hS : {xy : ZMod p × ZMod p // Wp.toAffine.Equation xy.1 xy.2} ≃
      {xy : ZMod p × ZMod p // xy.2 ^ 2 + (W.a₁ : ZMod p) * xy.1 * xy.2 + (W.a₃ : ZMod p) * xy.2 =
        xy.1 ^ 3 + (W.a₂ : ZMod p) * xy.1 ^ 2 + (W.a₄ : ZMod p) * xy.1 + (W.a₆ : ZMod p)} :=
    Equiv.subtypeEquivRight fun xy => by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp [Wp]
  change Nat.card (Option {xy : ZMod p × ZMod p // Wp.toAffine.Equation xy.1 xy.2}) = _
  rw [Finite.card_option, Nat.card_congr hS, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

end Arsenal.BSD
