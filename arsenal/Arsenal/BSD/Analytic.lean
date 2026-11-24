/-
Birch and Swinnerton-Dyer, the analytic side: the order of the zero at `s = 1` and its parity.
Released under the Apache License 2.0.
-/

import Mathlib

/-!
# The analytic side: the continuation, the order at `s = 1`, parity

Over any number field `K` (Mathlib's `W.LSeries` is defined there):

* `IsContinuation W Λ`: `Λ` is analytic on a half-plane `re s > a` with `a < 1` and equals Mathlib's L-series on some
  right half-plane. That is what BSD reads: the germ of the continuation at `s = 1`, reached from the region of
  convergence. Its existence is modularity over `ℚ` (open in general); not in Mathlib.
* `order_welldefined`: every continuation has the same order of zero at `s = 1` (identity theorem on the convex, hence
  connected, common half-plane).
* `order_parity`, `order_parity_of_factor`, `analytic_parity`: a local symmetry `ξ (2 - s) = w ξ s` near `s = 1`, with
  `ξ = G Λ` and `G` analytic and nonzero at `1`, forces `w = (-1)^(order of Λ at 1)`. The gamma factor and the conductor
  enter only through "analytic and nonzero at `1`".
* `FunctionalEquation K Λ w`: the completed function `ξ = A^{s/2} ((2π)^{-s} Γ(s))^{[K:ℚ]} Λ` satisfies
  `ξ (2 - s) = w ξ s` near `s = 1`, for some positive integer `A` (the conductor's norm times `d_K²`). The degree
  `[K:ℚ]` is the curve's field's; `A` is existential (the conductor is not in Mathlib, and parity does not read it);
  the root number `w` is not an input that the conclusions keep: it is forced to be `(-1)^order`.
-/

namespace Arsenal.BSD

open Filter Topology

/-! ## 1. Analytic facts about the order of a zero (no curve) -/

/-- **The zero at `s = 1` exists exactly when the order is positive** (for a function analytic at `1`). -/
theorem zero_iff_order_ne_zero {Λ : ℂ → ℂ} (hΛ : AnalyticAt ℂ Λ 1) :
    Λ 1 = 0 ↔ analyticOrderAt Λ 1 ≠ 0 := by
  rw [analyticOrderAt_ne_zero]
  exact ⟨fun h => ⟨hΛ, h⟩, fun h => h.2⟩

/-- **Parity from a local symmetry.** If `Λ` is analytic at `1`, `Λ (2 - s) = w Λ s` near `s = 1`, and the order
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

/-- **Parity through a factor**: if `G` is analytic and nonzero at `1` and the completed function `G Λ` satisfies
`ξ (2 - s) = w ξ s` near `s = 1`, then `w = (-1)^(order of Λ at 1)`. Which `G` it is does not matter. -/
theorem order_parity_of_factor {G Λ : ℂ → ℂ} (hG : AnalyticAt ℂ G 1) (hG1 : G 1 ≠ 0) (hΛ : AnalyticAt ℂ Λ 1)
    {w : ℂ} (hfe : ∀ᶠ s in 𝓝 (1 : ℂ), G (2 - s) * Λ (2 - s) = w * (G s * Λ s)) {n : ℕ}
    (hn : analyticOrderAt Λ 1 = n) : w = (-1) ^ n := by
  have h0 : analyticOrderAt G 1 = 0 := analyticOrderAt_eq_zero.2 (Or.inr hG1)
  have hm : analyticOrderAt (fun s => G s * Λ s) 1 = analyticOrderAt Λ 1 := by
    have := analyticOrderAt_mul hG hΛ
    rw [h0, zero_add] at this
    exact this
  exact order_parity (Λ := fun s => G s * Λ s) (hG.mul hΛ) hfe (hm.trans hn)

/-! ## 2. The gamma factor -/

/-- **The gamma factor** of an elliptic curve over a number field of degree `d`, with `A` the norm of the conductor times
the square of the field's discriminant: `A^{s/2} ((2π)^{-s} Γ(s))^d`. Over `ℚ`: `d = 1`, `A = N`. -/
noncomputable def gammaFactor (A d : ℕ) (s : ℂ) : ℂ :=
  (A : ℂ) ^ (s / 2) * ((2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s) ^ d

/-- Over `ℚ` the gamma factor is the familiar `N^{s/2} (2π)^{-s} Γ(s)`. -/
theorem gammaFactor_degree_one (N : ℕ) (s : ℂ) :
    gammaFactor N 1 s = (N : ℂ) ^ (s / 2) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s := by
  rw [gammaFactor, pow_one, mul_assoc]

/-- The gamma factor is analytic at `s = 1`. -/
theorem gammaFactor_analyticAt {A : ℕ} (hA : 0 < A) (d : ℕ) : AnalyticAt ℂ (gammaFactor A d) 1 := by
  have hU : {s : ℂ | 0 < s.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  refine DifferentiableOn.analyticAt (fun s hs => ?_) hU
  have hs' : ∀ m : ℕ, s ≠ -m := fun m h => by
    have : (0 : ℝ) < (-(m : ℂ)).re := h ▸ hs
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  exact (((differentiableAt_id.div_const 2).const_cpow (Or.inl hA')).mul
    (((differentiableAt_id.neg.const_cpow (Or.inl h2π)).mul
      (Complex.differentiableAt_Gamma s hs')).pow d)).differentiableWithinAt

/-- The gamma factor does not vanish at `s = 1`. -/
theorem gammaFactor_one_ne_zero {A : ℕ} (hA : 0 < A) (d : ℕ) : gammaFactor A d 1 ≠ 0 := by
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  unfold gammaFactor
  rw [Complex.Gamma_one, mul_one]
  exact mul_ne_zero (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num) |>.2 hA')
    (pow_ne_zero _ (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num) |>.2 h2π))

/-- **The completed function has the same order at `s = 1`** as the L-function (the gamma factor is analytic and nonzero
there). -/
theorem completed_order {A : ℕ} (hA : 0 < A) (d : ℕ) {Λ : ℂ → ℂ} (hΛ : AnalyticAt ℂ Λ 1) :
    analyticOrderAt (fun s => gammaFactor A d s * Λ s) 1 = analyticOrderAt Λ 1 := by
  have h0 : analyticOrderAt (gammaFactor A d) 1 = 0 :=
    analyticOrderAt_eq_zero.2 (Or.inr (gammaFactor_one_ne_zero hA d))
  have := analyticOrderAt_mul (gammaFactor_analyticAt hA d) hΛ
  rw [h0, zero_add] at this
  exact this

/-! ## 3. The curve: continuation and functional equation -/

section Curve

variable {K : Type*} [Field K] [NumberField K]

/-- **A continuation of the L-series to `s = 1`**: `Λ` is analytic on a half-plane `re s > a` with `a < 1` and equals
Mathlib's `W.LSeries` on some right half-plane `re s > σ`. Neither bound is fixed: the series converges for
`re s > 3/2` (Hasse's bound, not in Mathlib), and the identity theorem needs only some common half-plane. Over `ℚ`
the entire continuation exists by modularity (Wiles, Taylor-Wiles, Breuil-Conrad-Diamond-Taylor); not in Mathlib. -/
def IsContinuation (W : WeierstrassCurve K) (Λ : ℂ → ℂ) : Prop :=
  ∃ a : ℝ, a < 1 ∧ DifferentiableOn ℂ Λ {s : ℂ | a < s.re} ∧ ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Λ s = W.LSeries s

/-- An entire function equal to the L-series on `re s > 3/2` (the earlier, stronger form) is a continuation. -/
theorem IsContinuation.of_entire {W : WeierstrassCurve K} {Λ : ℂ → ℂ} (hd : Differentiable ℂ Λ)
    (h : ∀ s : ℂ, 3 / 2 < s.re → Λ s = W.LSeries s) : IsContinuation W Λ :=
  ⟨0, by norm_num, hd.differentiableOn, 3 / 2, h⟩

/-- A continuation is analytic at `s = 1`. -/
theorem IsContinuation.analyticAt_one {W : WeierstrassCurve K} {Λ : ℂ → ℂ} (h : IsContinuation W Λ) :
    AnalyticAt ℂ Λ 1 := by
  obtain ⟨a, ha, hd, -⟩ := h
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show a < (1 : ℂ).re by rw [Complex.one_re]; exact ha))

/-- **The continuation is unique near `s = 1`**: two continuations agree on a neighbourhood of `1` (the identity theorem
on the half-plane `re s > max a₁ a₂`, which is convex and contains `1`). -/
theorem continuation_unique {W : WeierstrassCurve K} {Λ₁ Λ₂ : ℂ → ℂ} (h₁ : IsContinuation W Λ₁)
    (h₂ : IsContinuation W Λ₂) : Λ₁ =ᶠ[𝓝 (1 : ℂ)] Λ₂ := by
  obtain ⟨a₁, ha₁, d₁, σ₁, e₁⟩ := h₁
  obtain ⟨a₂, ha₂, d₂, σ₂, e₂⟩ := h₂
  have hopen : ∀ b : ℝ, IsOpen {s : ℂ | b < s.re} := fun b => isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ Λ₁ {s : ℂ | max a₁ a₂ < s.re} := fun z hz =>
    d₁.analyticAt ((hopen a₁).mem_nhds (show a₁ < z.re from lt_of_le_of_lt (le_max_left _ _) hz))
  have hg : AnalyticOnNhd ℂ Λ₂ {s : ℂ | max a₁ a₂ < s.re} := fun z hz =>
    d₂.analyticAt ((hopen a₂).mem_nhds (show a₂ < z.re from lt_of_le_of_lt (le_max_right _ _) hz))
  have hb : ((max (max σ₁ σ₂) (max a₁ a₂) + 1 : ℝ) : ℂ) ∈ {s : ℂ | max a₁ a₂ < s.re} := by
    show max a₁ a₂ < (((max (max σ₁ σ₂) (max a₁ a₂) + 1 : ℝ)) : ℂ).re
    rw [Complex.ofReal_re]; linarith [le_max_right (max σ₁ σ₂) (max a₁ a₂)]
  have hfg : Λ₁ =ᶠ[𝓝 ((max (max σ₁ σ₂) (max a₁ a₂) + 1 : ℝ) : ℂ)] Λ₂ := by
    have hσ : {s : ℂ | max σ₁ σ₂ < s.re} ∈ 𝓝 ((max (max σ₁ σ₂) (max a₁ a₂) + 1 : ℝ) : ℂ) := by
      refine (hopen _).mem_nhds ?_
      show max σ₁ σ₂ < (((max (max σ₁ σ₂) (max a₁ a₂) + 1 : ℝ)) : ℂ).re
      rw [Complex.ofReal_re]; linarith [le_max_left (max σ₁ σ₂) (max a₁ a₂)]
    filter_upwards [hσ] with s hs
    rw [e₁ s (lt_of_le_of_lt (le_max_left _ _) hs), e₂ s (lt_of_le_of_lt (le_max_right _ _) hs)]
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt _).isPreconnected hb hfg
  have h1 : {s : ℂ | max a₁ a₂ < s.re} ∈ 𝓝 (1 : ℂ) :=
    (hopen _).mem_nhds (show max a₁ a₂ < (1 : ℂ).re by rw [Complex.one_re]; exact max_lt ha₁ ha₂)
  filter_upwards [h1] with s hs using heq hs

/-- **The analytic rank is well defined**: every continuation has the same order of zero at `s = 1`. -/
theorem order_welldefined {W : WeierstrassCurve K} {Λ₁ Λ₂ : ℂ → ℂ} (h₁ : IsContinuation W Λ₁)
    (h₂ : IsContinuation W Λ₂) : analyticOrderAt Λ₁ 1 = analyticOrderAt Λ₂ 1 :=
  analyticOrderAt_congr (continuation_unique h₁ h₂)

variable (K) in
/-- **The functional equation near `s = 1`**: for some positive integer `A` (the norm of the conductor times `d_K²`), the
completed function `ξ s = gammaFactor A [K:ℚ] s · Λ s` satisfies `ξ (2 - s) = w ξ s` near `s = 1`. Over `ℚ` it holds on
all of `ℂ` with `A` the conductor, by modularity; not in Mathlib. Parity reads only the germ at `s = 1`. -/
def FunctionalEquation (Λ : ℂ → ℂ) (w : ℂ) : Prop :=
  ∃ A : ℕ, 0 < A ∧ ∀ᶠ s in 𝓝 (1 : ℂ),
    gammaFactor A (Module.finrank ℚ K) (2 - s) * Λ (2 - s) = w * (gammaFactor A (Module.finrank ℚ K) s * Λ s)

/-- **Parity of the analytic rank** (from the functional equation): `w = (-1)^(order of Λ at 1)`. -/
theorem analytic_parity {Λ : ℂ → ℂ} (hΛ : AnalyticAt ℂ Λ 1) {w : ℂ} (hfe : FunctionalEquation K Λ w) {n : ℕ}
    (hn : analyticOrderAt Λ 1 = n) : w = (-1) ^ n := by
  obtain ⟨A, hA, h⟩ := hfe
  exact order_parity_of_factor (gammaFactor_analyticAt hA _) (gammaFactor_one_ne_zero hA _) hΛ h hn

end Curve

/-- The functional equation over `ℚ` on the strip `0 < re s < 2` with conductor `N` (the earlier, stronger form) gives
the local one. -/
theorem FunctionalEquation.of_strip {Λ : ℂ → ℂ} {w : ℂ} {N : ℕ} (hN : 0 < N)
    (h : ∀ s : ℂ, 0 < s.re → s.re < 2 → gammaFactor N 1 (2 - s) * Λ (2 - s) = w * (gammaFactor N 1 s * Λ s)) :
    FunctionalEquation ℚ Λ w := by
  have hU : {s : ℂ | 0 < s.re ∧ s.re < 2} ∈ 𝓝 (1 : ℂ) :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds (by norm_num)
  refine ⟨N, hN, ?_⟩
  simp only [Module.finrank_self]
  filter_upwards [hU] with s hs
  exact h s hs.1 hs.2

end Arsenal.BSD
