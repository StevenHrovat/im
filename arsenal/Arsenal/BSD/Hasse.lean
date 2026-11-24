/-
Birch and Swinnerton-Dyer: Hasse's bound, named, and what it gives.
Released under the Apache License 2.0.
-/

import Mathlib
import Arsenal.R136a1
import Arsenal.BSD.Analytic
import Arsenal.BSD.Count

/-!
# Hasse's bound and the finite order at `s = 1`

Hasse's bound `a_v² ≤ 4 q_v` says that Frobenius at a place of good reduction acts as a rotation: its eigenvalues lie on
the circle of radius `√q_v`. Its proof is one positivity: the degree is a positive definite quadratic form on `End(E)`, so
`deg(m - n φ) = m² - a m n + q n² ≥ 0` for all integers `m, n`, and the discriminant `a² - 4q` is `≤ 0` (Silverman V.1.1).
Mathlib has neither isogeny degrees nor intersection theory on `E × E`, so it is named here: `Hasse W`, answered R136a1.

What it gives, proved:

* `quad_bound`: if `a² ≤ 4q`, the coefficients of `1 / (1 - a T + q T²)` satisfy `|c_k| ≤ (k + 1) q^{k/2}`
  (`c_k = Σ α^i β^{k-i}` with `|α| = |β| = √q`, the rotation);
* `localPowerSeries_coeff_bound`: so every local factor of Mathlib's `W.LFunction` has coefficients at most
  `max 1 ((k + 1) q_v^{k/2})` (the bad places give `|c_k| ≤ 1`);
* `LFunction_one`: the first coefficient of `W.LFunction` is `1`;
* `order_ne_top_of_summable`: if the L-series converges absolutely anywhere, every continuation has a finite order at
  `s = 1` (an L-series with first coefficient `1` is not eventually zero, `LSeries_not_eventually_zero`; the identity
  theorem carries that to `s = 1`).

What is left, named: `EulerProductBound K`, that an Euler product over the primes of `K` whose local factors have these
coefficient bounds converges absolutely for `re s > 3/2` (it is dominated by `ζ_K(s - 1/2)²`). With it,
`order_ne_top` gives a finite order from `Hasse` alone.
-/

namespace Arsenal.BSD

open Filter Topology

/-! ## 1. The coefficients of `1 / (1 - a T + q T²)` -/

/-- The inverse of the local polynomial `1 - a T + q T²`, as a power series over `ℤ`. -/
noncomputable def invQuad (a q : ℤ) : PowerSeries ℤ :=
  PowerSeries.invOfUnit
    ((1 - Polynomial.C a * Polynomial.X + Polynomial.C q * Polynomial.X ^ 2 : Polynomial ℤ) : PowerSeries ℤ) 1

/-- **The recurrence**: `c_0 = 1`, `c_1 = a`, `c_{k+2} = a c_{k+1} - q c_k`. -/
theorem invQuad_coeff (a q : ℤ) :
    PowerSeries.coeff 0 (invQuad a q) = 1 ∧ PowerSeries.coeff 1 (invQuad a q) = a ∧
      ∀ k, PowerSeries.coeff (k + 2) (invQuad a q) =
        a * PowerSeries.coeff (k + 1) (invQuad a q) - q * PowerSeries.coeff k (invQuad a q) := by
  set P : PowerSeries ℤ :=
    ((1 - Polynomial.C a * Polynomial.X + Polynomial.C q * Polynomial.X ^ 2 : Polynomial ℤ) : PowerSeries ℤ) with hPdef
  have hP : P = 1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C q * PowerSeries.X ^ 2 := by
    rw [hPdef, Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
  have hc : PowerSeries.constantCoeff P = ((1 : ℤˣ) : ℤ) := by rw [hP]; simp
  have hPQ : P * invQuad a q = 1 := PowerSeries.mul_invOfUnit P 1 hc
  set Q := invQuad a q with hQ
  have hexp : P * Q = Q - PowerSeries.C a * (PowerSeries.X * Q) +
      PowerSeries.C q * (PowerSeries.X * (PowerSeries.X * Q)) := by rw [hP]; ring
  have key : ∀ n, PowerSeries.coeff n Q - a * PowerSeries.coeff n (PowerSeries.X * Q) +
      q * PowerSeries.coeff n (PowerSeries.X * (PowerSeries.X * Q)) = PowerSeries.coeff n (1 : PowerSeries ℤ) := by
    intro n
    rw [← hPQ, hexp, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  have h0 : PowerSeries.coeff 0 Q = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hQ, invQuad, PowerSeries.constantCoeff_invOfUnit]
    simp
  refine ⟨h0, ?_, fun k => ?_⟩
  · have e1 : PowerSeries.coeff 1 (PowerSeries.X * Q) = PowerSeries.coeff 0 Q := PowerSeries.coeff_succ_X_mul 0 Q
    have e2 : PowerSeries.coeff 1 (PowerSeries.X * (PowerSeries.X * Q)) = PowerSeries.coeff 0 (PowerSeries.X * Q) :=
      PowerSeries.coeff_succ_X_mul 0 _
    have e3 : PowerSeries.coeff 0 (PowerSeries.X * Q) = 0 := PowerSeries.coeff_zero_X_mul Q
    have h := key 1
    rw [e1, e2, e3, h0, PowerSeries.coeff_one] at h
    simp at h
    linarith
  · have e1 : PowerSeries.coeff (k + 2) (PowerSeries.X * Q) = PowerSeries.coeff (k + 1) Q :=
      PowerSeries.coeff_succ_X_mul (k + 1) Q
    have e2 : PowerSeries.coeff (k + 2) (PowerSeries.X * (PowerSeries.X * Q)) =
        PowerSeries.coeff (k + 1) (PowerSeries.X * Q) := PowerSeries.coeff_succ_X_mul (k + 1) _
    have e3 : PowerSeries.coeff (k + 1) (PowerSeries.X * Q) = PowerSeries.coeff k Q := PowerSeries.coeff_succ_X_mul k Q
    have h := key (k + 2)
    rw [e1, e2, e3, PowerSeries.coeff_one] at h
    simp at h
    linarith

/-- **The rotation bound.** A sequence with `c_0 = 1`, `c_1 = a`, `c_{k+2} = a c_{k+1} - q c_k` and `a² ≤ 4q` satisfies
`|c_k| ≤ (k + 1) √q^k`: it is `Σ_{i ≤ k} α^i β^{k-i}` for the two roots `α`, `β = ᾱ` of `T² - a T + q`, which lie on the
circle of radius `√q`. -/
theorem quad_bound {a q : ℤ} (hH : a ^ 2 ≤ 4 * q) (c : ℕ → ℤ) (h0 : c 0 = 1) (h1 : c 1 = a)
    (hrec : ∀ k, c (k + 2) = a * c (k + 1) - q * c k) (k : ℕ) :
    |(c k : ℝ)| ≤ (k + 1) * Real.sqrt q ^ k := by
  have hH' : (a : ℝ) ^ 2 ≤ 4 * q := by exact_mod_cast hH
  have ht0 : (0 : ℝ) ≤ q - (a : ℝ) ^ 2 / 4 := by linarith
  have hq : (0 : ℝ) ≤ q := by nlinarith [sq_nonneg (a : ℝ)]
  set t := Real.sqrt ((q : ℝ) - (a : ℝ) ^ 2 / 4) with ht_def
  have ht : t * t = q - (a : ℝ) ^ 2 / 4 := Real.mul_self_sqrt ht0
  set α : ℂ := ⟨a / 2, t⟩ with hα
  set β : ℂ := ⟨a / 2, -t⟩ with hβ
  have hsum : α + β = a := by apply Complex.ext <;> simp [α, β]
  have hprod : α * β = q := by
    apply Complex.ext
    · simp only [α, β, Complex.mul_re, Complex.intCast_re]; nlinarith [ht]
    · simp only [α, β, Complex.mul_im, Complex.intCast_im]; ring
  have hnα : ‖α‖ = Real.sqrt q := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; simp only [α]; nlinarith [ht]
  have hnβ : ‖β‖ = Real.sqrt q := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; simp only [β]; nlinarith [ht]
  set d : ℕ → ℂ := fun k => ∑ i ∈ Finset.range (k + 1), α ^ i * β ^ (k - i) with hd
  have hd_succ : ∀ k, d (k + 1) = α ^ (k + 1) + β * d k := by
    intro k
    simp only [hd]
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have : k + 1 - i = (k - i) + 1 := by have := Finset.mem_range.1 hi; omega
    rw [this, pow_succ]; ring
  have hd0 : d 0 = 1 := by simp [hd]
  have hd1 : d 1 = a := by rw [hd_succ, hd0, pow_one, mul_one, hsum]
  have hd_rec : ∀ k, d (k + 2) = a * d (k + 1) - q * d k := by
    intro k
    show d (k + 1 + 1) = _
    rw [hd_succ (k + 1), hd_succ k, ← hsum, ← hprod]; ring
  have hcd : ∀ k, (c k : ℂ) = d k ∧ (c (k + 1) : ℂ) = d (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨by rw [h0, hd0]; simp, by rw [h1, hd1]⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      show (c (k + 2) : ℂ) = d (k + 2)
      rw [hrec, hd_rec, ← ih.1, ← ih.2]; push_cast; ring
  have hbound : ‖d k‖ ≤ (k + 1) * Real.sqrt q ^ k := by
    calc ‖d k‖ ≤ ∑ i ∈ Finset.range (k + 1), ‖α ^ i * β ^ (k - i)‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range (k + 1), Real.sqrt q ^ k := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [norm_mul, norm_pow, norm_pow, hnα, hnβ, ← pow_add]
          congr 1; have := Finset.mem_range.1 hi; omega
      _ = (k + 1) * Real.sqrt q ^ k := by simp
  calc |(c k : ℝ)| = ‖(c k : ℂ)‖ := by rw [Complex.norm_intCast]
    _ = ‖d k‖ := by rw [(hcd k).1]
    _ ≤ _ := hbound

/-- **The bad places**: with `q = 0` and `|a| ≤ 1` (multiplicative or additive reduction), `|c_k| ≤ 1`. -/
theorem lin_bound {a : ℤ} (ha : |a| ≤ 1) (c : ℕ → ℤ) (h0 : c 0 = 1) (h1 : c 1 = a)
    (hrec : ∀ k, c (k + 2) = a * c (k + 1) - 0 * c k) (k : ℕ) : |(c k : ℝ)| ≤ 1 := by
  have : ∀ k, |c k| ≤ 1 ∧ |c (k + 1)| ≤ 1 := by
    intro k
    induction k with
    | zero => exact ⟨by rw [h0]; simp, by rw [h1]; exact ha⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      show |c (k + 2)| ≤ 1
      rw [hrec, zero_mul, sub_zero, abs_mul]
      nlinarith [abs_nonneg a, abs_nonneg (c (k + 1)), ih.2]
  have h := (this k).1
  rw [← Int.cast_abs]
  exact_mod_cast h

theorem invQuad_bound {a q : ℤ} (hH : a ^ 2 ≤ 4 * q) (k : ℕ) :
    |((PowerSeries.coeff k (invQuad a q) : ℤ) : ℝ)| ≤ (k + 1) * Real.sqrt q ^ k :=
  let h := invQuad_coeff a q
  quad_bound hH (fun k => PowerSeries.coeff k (invQuad a q)) h.1 h.2.1 h.2.2 k

theorem invQuad_bound_lin {a : ℤ} (ha : |a| ≤ 1) (k : ℕ) : |((PowerSeries.coeff k (invQuad a 0) : ℤ) : ℝ)| ≤ 1 :=
  let h := invQuad_coeff a 0
  lin_bound ha (fun k => PowerSeries.coeff k (invQuad a 0)) h.1 h.2.1 h.2.2 k

/-! ## 2. One place: Mathlib's local factor -/

section Local

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {Kv : Type*} [Field Kv] [Algebra R Kv]
  [IsFractionRing R Kv]

/-- **Hasse's bound at one place**, in exactly the terms of Mathlib's local polynomial: if the minimal model has good
reduction, the trace of Frobenius `a = q + 1 - #E(κ)` satisfies `a² ≤ 4 q`, with `q` the size of the residue field `κ`
(over a finite field this is `hasseCheck`, `hasseCheck_iff_card`). -/
def LocalHasse (W : WeierstrassCurve Kv) : Prop :=
  (W.minimal R).HasGoodReduction R →
    ((Nat.card (IsLocalRing.ResidueField R) : ℤ) + 1 - Nat.card ((W.minimal R).reduction R).toAffine.Point) ^ 2 ≤
      4 * (Nat.card (IsLocalRing.ResidueField R) : ℤ)

/-- The local power series starts with `1`. -/
theorem localPowerSeries_coeff_zero (W : WeierstrassCurve Kv) : PowerSeries.coeff 0 (W.localPowerSeries R) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, WeierstrassCurve.localPowerSeries,
    PowerSeries.constantCoeff_invOfUnit]
  simp

/-- **The local coefficient bound**: under Hasse at this place, the coefficients of Mathlib's local power series are at
most `max 1 ((k + 1) q^{k/2})`. -/
theorem localPowerSeries_coeff_bound (W : WeierstrassCurve Kv) (h : LocalHasse R W) (k : ℕ) :
    |((PowerSeries.coeff k (W.localPowerSeries R) : ℤ) : ℝ)| ≤
      max 1 ((k + 1) * Real.sqrt (Nat.card (IsLocalRing.ResidueField R)) ^ k) := by
  unfold WeierstrassCurve.localPowerSeries WeierstrassCurve.localPolynomial
  split_ifs with hg hs hm
  · have := invQuad_bound (h hg) k
    rw [Int.cast_natCast] at this
    exact le_max_of_le_right this
  · rw [show (1 - Polynomial.X : Polynomial ℤ) =
      1 - Polynomial.C 1 * Polynomial.X + Polynomial.C 0 * Polynomial.X ^ 2 by simp]
    exact le_max_of_le_left (invQuad_bound_lin (by norm_num) k)
  · rw [show (1 + Polynomial.X : Polynomial ℤ) =
      1 - Polynomial.C (-1) * Polynomial.X + Polynomial.C 0 * Polynomial.X ^ 2 by simp]
    exact le_max_of_le_left (invQuad_bound_lin (by norm_num) k)
  · rw [show (1 : Polynomial ℤ) =
      1 - Polynomial.C 0 * Polynomial.X + Polynomial.C 0 * Polynomial.X ^ 2 by simp]
    exact le_max_of_le_left (invQuad_bound_lin (by norm_num) k)

end Local

/-- Over a finite field, the local form of Hasse is the decidable check `hasseCheck` of `Arsenal.BSD.Count`. -/
theorem hasseCheck_iff_card {F : Type*} [Field F] [Fintype F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic] :
    hasseCheck W = true ↔ ((Nat.card F : ℤ) + 1 - Nat.card (Pts W)) ^ 2 ≤ 4 * (Nat.card F : ℤ) := by
  unfold hasseCheck frobTrace
  rw [decide_eq_true_iff, count_correct, Nat.card_eq_fintype_card]

/-! ## 3. The first coefficient, and a finite order -/

/-- An Euler product of factors starting with `1` starts with `1`. -/
theorem eulerProduct_apply_one {ι R : Type*} [CommSemiring R] (f : ι → ArithmeticFunction R) (hf : ∀ i, f i 1 = 1) :
    ArithmeticFunction.eulerProduct f 1 = 1 := by
  classical
  let : UniformSpace (ArithmeticFunction R) := ArithmeticFunction.uniformSpace
  have hfin : ∀ s : Finset ι, (∏ i ∈ s, f i) 1 = 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one, Finset.sum_singleton,
        hf, ih, one_mul]
  by_cases hm : Multipliable f
  · let : UniformSpace R := ⊥
    have hI : IsUniformInducing ((↑) : ArithmeticFunction R → (ℕ → R)) := ⟨rfl⟩
    have h1 := hI.isInducing.tendsto_nhds_iff.1 hm.hasProd
    have h2 := tendsto_pi_nhds.1 h1 1
    have : DiscreteTopology R := ⟨rfl⟩
    rw [nhds_discrete, tendsto_pure] at h2
    obtain ⟨s, hs⟩ := h2.exists
    simp only [Function.comp_apply] at hs
    rw [ArithmeticFunction.eulerProduct, ← hs, hfin]
  · rw [ArithmeticFunction.eulerProduct, tprod_eq_one_of_not_multipliable hm]
    exact ArithmeticFunction.one_one

/-- An L-series with nonzero first coefficient that converges absolutely somewhere is not zero for all large real
arguments. -/
theorem LSeries_not_eventually_zero {f : ℕ → ℂ} (h1 : f 1 ≠ 0) {s : ℂ} (hs : LSeriesSummable f s) :
    ¬ (fun x : ℝ => LSeries f x) =ᶠ[atTop] 0 := by
  rw [LSeries_eventually_eq_zero_iff']
  rintro (h | h)
  · exact h1 (h 1 one_ne_zero)
  · have := hs.abscissaOfAbsConv_le
    rw [h] at this
    exact absurd this (by simp)

/-- **A finite order at `s = 1`** for any `Λ` analytic on a half-plane containing `1` that continues an L-series with
nonzero first coefficient converging absolutely somewhere. -/
theorem order_ne_top_of_LSeries {f : ℕ → ℂ} (h1 : f 1 ≠ 0) {s : ℂ} (hs : LSeriesSummable f s) {Λ : ℂ → ℂ} {a : ℝ}
    (ha : a < 1) (hd : DifferentiableOn ℂ Λ {z : ℂ | a < z.re}) {σ : ℝ} (he : ∀ z : ℂ, σ < z.re → Λ z = LSeries f z) :
    analyticOrderAt Λ 1 ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hopen : IsOpen {z : ℂ | a < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hA : AnalyticOnNhd ℂ Λ {z : ℂ | a < z.re} := fun z hz => hd.analyticAt (hopen.mem_nhds hz)
  have h1U : (1 : ℂ) ∈ {z : ℂ | a < z.re} := show a < (1 : ℂ).re by rw [Complex.one_re]; exact ha
  have hz := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_halfSpace_re_gt a).isPreconnected h1U htop
  apply LSeries_not_eventually_zero h1 hs
  filter_upwards [eventually_gt_atTop (max σ a)] with x hx
  have hxσ : σ < ((x : ℂ)).re := by rw [Complex.ofReal_re]; exact lt_of_le_of_lt (le_max_left _ _) hx
  have hxa : a < ((x : ℂ)).re := by rw [Complex.ofReal_re]; exact lt_of_le_of_lt (le_max_right _ _) hx
  rw [← he x hxσ, hz hxa]
  rfl

/-! ## 4. The curve -/

section NumberField

open IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Hasse's bound** for a curve over a number field: at every prime of good reduction, the trace of Frobenius of the
reduced curve satisfies `a_v² ≤ 4 q_v`, in Mathlib's terms (the minimal model over the completion, its reduction, the
residue field). Proved by Hasse (1933-36); its proof (the degree is a positive definite quadratic form on `End(E)`,
Silverman V.1.1) needs isogeny degrees, which Mathlib lacks. Named, answered R136a1 where used. -/
def Hasse (W : WeierstrassCurve K) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), LocalHasse (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K))

/-- The coefficients of Mathlib's L-function of `W`, as complex numbers. -/
noncomputable abbrev lcoeff (W : WeierstrassCurve K) (n : ℕ) : ℂ := (W.LFunction n : ℂ)

theorem LSeries_eq (W : WeierstrassCurve K) (s : ℂ) : W.LSeries s = LSeries (lcoeff W) s := rfl

/-- **The first coefficient of `W.LFunction` is `1`**: every local factor starts with `1`. -/
theorem LFunction_one (W : WeierstrassCurve K) : W.LFunction 1 = 1 :=
  eulerProduct_apply_one _ fun v => by
    rw [WeierstrassCurve.localEulerFactor, ArithmeticFunction.ofPowerSeries_apply_one,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, localPowerSeries_coeff_zero]

/-- **Every continuation has a finite order at `s = 1`** once the L-series converges absolutely somewhere. -/
theorem order_ne_top_of_summable {W : WeierstrassCurve K} {Λ : ℂ → ℂ} (hΛ : IsContinuation W Λ) {s : ℂ}
    (hs : LSeriesSummable (lcoeff W) s) : analyticOrderAt Λ 1 ≠ ⊤ := by
  obtain ⟨a, ha, hd, σ, he⟩ := hΛ
  exact order_ne_top_of_LSeries (by simp [lcoeff, LFunction_one]) hs ha hd he

variable (K) in
/-- **The Euler product step** (named, the one piece left between Hasse and convergence): an Euler product over the
primes of `K` whose local factors `Σ c_{v,k} q_v^{-ks}` start with `1` and have `|c_{v,k}| ≤ max 1 ((k + 1) q_v^{k/2})`
converges absolutely for `re s > 3/2`. Classical: it is dominated term by term by `ζ_K(s - 1/2)²`. Not proved here: it
needs the coefficients of an infinite Euler product (Mathlib's `eulerProduct` API gives them only through
`tendsTo_eulerProduct_of_tendsTo`), the residue fields of the completions identified with `𝓞 K / v` (so `q_v` is the
absolute norm and only finitely many `v` have `q_v ≤ n`), and the convergence of `ζ_K` for `re s > 1`. -/
def EulerProductBound : Prop :=
  ∀ c : HeightOneSpectrum (𝓞 K) → PowerSeries ℤ, (∀ v, PowerSeries.coeff 0 (c v) = 1) →
    (∀ v k, |((PowerSeries.coeff k (c v) : ℤ) : ℝ)| ≤
      max 1 ((k + 1) * Real.sqrt (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K))) ^ k)) →
    ∀ s : ℂ, 3 / 2 < s.re → LSeriesSummable (fun n => ((ArithmeticFunction.eulerProduct fun v =>
      ArithmeticFunction.ofPowerSeries (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K))) (c v)) n : ℂ)) s

/-- **Hasse gives absolute convergence for `re s > 3/2`**, through the named Euler product step. -/
theorem LSeriesSummable_of_hasse (W : WeierstrassCurve K) (hH : R136a1 "Hasse" (Hasse W))
    (hE : R136a1 "Euler product bound" (EulerProductBound K)) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable (lcoeff W) s :=
  hE.out (fun v => (W.baseChange (v.adicCompletion K)).localPowerSeries (v.adicCompletionIntegers K))
    (fun _ => localPowerSeries_coeff_zero _ _)
    (fun v k => localPowerSeries_coeff_bound _ _ (hH.out v) k) s hs

/-- **Hasse gives a finite order at `s = 1`**: every continuation of the L-series of `W` has a zero of finite order there. -/
theorem order_ne_top {W : WeierstrassCurve K} {Λ : ℂ → ℂ} (hΛ : IsContinuation W Λ)
    (hH : R136a1 "Hasse" (Hasse W)) (hE : R136a1 "Euler product bound" (EulerProductBound K)) :
    analyticOrderAt Λ 1 ≠ ⊤ :=
  order_ne_top_of_summable hΛ (LSeriesSummable_of_hasse W hH hE (s := 2) (by norm_num))

/-- **Parity of the analytic rank, with no order given separately**: `w = (-1)^(order of Λ at 1)`. -/
theorem analytic_parity_of_hasse {W : WeierstrassCurve K} {Λ : ℂ → ℂ} (hΛ : IsContinuation W Λ) {w : ℂ}
    (hfe : FunctionalEquation K Λ w) (hH : R136a1 "Hasse" (Hasse W))
    (hE : R136a1 "Euler product bound" (EulerProductBound K)) :
    w = (-1) ^ (analyticOrderAt Λ 1).toNat :=
  analytic_parity hΛ.analyticAt_one hfe (ENat.natCast_toNat (order_ne_top hΛ hH hE)).symm

end NumberField

end Arsenal.BSD
