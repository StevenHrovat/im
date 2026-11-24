/-
Birch and Swinnerton-Dyer: the Euler product bound over the rationals, proved.
Released under the Apache License 2.0.
-/

import Mathlib
import Arsenal.BSD.Hasse

/-!
# The Euler product bound over `ℚ`

`EulerProductBound K` (Hasse.lean) is the named step between Hasse's bound and absolute convergence: an Euler product over
the primes of `K` whose local factors start with `1` and have coefficients `|c_{v,k}| ≤ max 1 ((k + 1) q_v^{k/2})` converges
absolutely for `re s > 3/2`. Over `ℚ` it is proved here, so for a curve over `ℚ` only `Hasse` stays named.

The proof, in the order of the file:

* `prime_pow_mul_apply`: if `b` is trivial at a prime `p` (`b 1 = 1`, `b (p^j) = 0` for `j ≥ 1`), then `(a * b)(p^k) = a(p^k)`;
* `ofPowerSeries_prime_pow_of_ne`: the factor at a prime `q ≠ p` is trivial at `p`;
* `eulerProduct_prime_pow`: for an injective family of primes `P`, the Euler product at `p^k` is the `k`-th coefficient of
  the factor at `p` (and `0` when no factor sits at `p`); `isMultiplicative_eulerProduct_primes`: it is multiplicative;
* `abs_eulerProduct_le`: so `|F n| ≤ d(n) √n`, `d(n)` the number of divisors (both sides multiplicative);
* `lseriesSummable_eulerProduct_primes`: and `Σ |F n| n^{-σ} ≤ Σ d(n) n^{-(σ - 1/2)}`, which converges for `σ > 3/2`
  because `d = ζ * ζ` (Mathlib's `LSeriesSummable_zeta_iff`, `LSeriesSummable_mul`);
* `card_residueField_rat`: at a prime `v` of `𝓞 ℚ` the residue field of the completion has `p_v` elements
  (`padicIntEquiv`, `PadicInt.residueField`), and `v ↦ p_v` is a bijection onto the primes (`primesEquiv`);
* `eulerProductBound_rat`: **`EulerProductBound ℚ`**;
* `LSeriesSummable_of_hasse_rat`, `order_ne_top_rat`, `analytic_parity_of_hasse_rat`: Hasse.lean's consequences over `ℚ`
  from `Hasse` alone.

Over a number field of degree `> 1` several primes lie over one rational prime and `q_v = p^f`; that case stays named.
-/

namespace Arsenal.BSD

open ArithmeticFunction IsDedekindDomain NumberField Filter
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma LSeries.notation

/-! ## 1. Prime powers in a Dirichlet product -/

/-- `b` is trivial at the prime `p`: `b 1 = 1` and `b` vanishes on the positive powers of `p`. -/
def TrivialAt {R : Type*} [Semiring R] (b : ArithmeticFunction R) (p : ℕ) : Prop :=
  b 1 = 1 ∧ ∀ j, j ≠ 0 → b (p ^ j) = 0

/-- **A factor trivial at `p` does not change the values at the powers of `p`.** -/
theorem prime_pow_mul_apply {R : Type*} [Semiring R] {p : ℕ} (hp : p.Prime) (a b : ArithmeticFunction R)
    (hb : TrivialAt b p) (k : ℕ) : (a * b) (p ^ k) = a (p ^ k) := by
  rw [mul_apply, Finset.sum_eq_single (p ^ k, 1)]
  · simp [hb.1]
  · rintro ⟨x, y⟩ hxy hne
    rw [Nat.mem_divisorsAntidiagonal] at hxy
    obtain ⟨hxy, -⟩ := hxy
    change x * y = p ^ k at hxy
    by_cases hy : y = 1
    · subst hy
      exact absurd (by simpa using hxy) hne
    · have hyd : y ∣ p ^ k := ⟨x, by rw [← hxy]; ring⟩
      obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hyd
      have hj : j ≠ 0 := by rintro rfl; exact hy (pow_zero p)
      simp [hb.2 j hj]
  · intro h
    exact absurd (Nat.mem_divisorsAntidiagonal.2 ⟨by simp, pow_ne_zero k hp.ne_zero⟩) h

/-- The identity is trivial at every prime. -/
theorem trivialAt_one {R : Type*} [Semiring R] {p : ℕ} (hp : p.Prime) : TrivialAt (1 : ArithmeticFunction R) p :=
  ⟨one_one, fun j hj => one_apply_ne (by
    intro h; exact hj ((Nat.pow_eq_one.1 h).resolve_left hp.ne_one))⟩

/-- A product of factors trivial at `p` is trivial at `p`. -/
theorem trivialAt_mul {R : Type*} [CommSemiring R] {p : ℕ} (hp : p.Prime) {a b : ArithmeticFunction R}
    (ha : TrivialAt a p) (hb : TrivialAt b p) : TrivialAt (a * b) p := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [← pow_zero p, prime_pow_mul_apply hp a b hb 0, pow_zero, ha.1]
  · rw [prime_pow_mul_apply hp a b hb j, ha.2 j hj]

/-- **The factor at a prime `q ≠ p` is trivial at `p`.** -/
theorem ofPowerSeries_trivialAt {R : Type*} [CommSemiring R] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : q ≠ p)
    (f : PowerSeries R) (hf : PowerSeries.coeff 0 f = 1) : TrivialAt (ofPowerSeries q f) p := by
  refine ⟨by rw [ofPowerSeries_apply_one, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf], fun j hj => ?_⟩
  rw [ofPowerSeries_apply hq.one_lt, Function.extend_apply', Pi.zero_apply]
  rintro ⟨i, hi⟩
  change q ^ i = p ^ j at hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [pow_zero] at hi
    exact hj ((Nat.pow_eq_one.1 hi.symm).resolve_left hp.ne_one)
  · have : p ∣ q := hp.dvd_of_dvd_pow (show p ∣ q ^ i by rw [hi]; exact dvd_pow_self p hj)
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 this).symm

/-! ## 2. Euler products over an injective family of primes -/

variable {ι : Type*} (P : ι → Nat.Primes) (c : ι → PowerSeries ℤ)

/-- The Euler factors at the primes `P i`. -/
noncomputable abbrev factors : ι → ArithmeticFunction ℤ := fun i => ofPowerSeries (P i : ℕ) (c i)

theorem northcott_primes (hP : Function.Injective P) : Northcott (fun i => (P i : ℕ)) := by
  refine ⟨fun b => ?_⟩
  have hfin : {p : Nat.Primes | (p : ℕ) ≤ b}.Finite :=
    (Set.finite_Iic b).preimage fun _ _ _ _ h => Subtype.val_injective h
  exact hfin.preimage fun _ _ _ _ h => hP h

variable {P c}

theorem isMultiplicative_eulerProduct_primes (hc : ∀ i, PowerSeries.coeff 0 (c i) = 1) :
    IsMultiplicative (eulerProduct (factors P c)) :=
  isMultiplicative_eulerProduct _ fun i => isMultiplicative_ofPowerSeries_of_isPrimePow _ (P i).2.isPrimePow _
    (by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hc i])

/-- A finite product of factors at primes other than `p` is trivial at `p`. -/
theorem prod_trivialAt (hc : ∀ i, PowerSeries.coeff 0 (c i) = 1) {p : ℕ} (hp : p.Prime) (t : Finset ι)
    (ht : ∀ i ∈ t, (P i : ℕ) ≠ p) : TrivialAt (∏ i ∈ t, factors P c i) p := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using trivialAt_one hp
  | insert i t hi ih =>
    rw [Finset.prod_insert hi]
    exact trivialAt_mul hp (ofPowerSeries_trivialAt hp (P i).2 (ht i (Finset.mem_insert_self i t)) _ (hc i))
      (ih fun j hj => ht j (Finset.mem_insert_of_mem hj))

/-- **The Euler product at a prime power** is the coefficient of the factor at that prime. -/
theorem eulerProduct_prime_pow (hP : Function.Injective P) (hc : ∀ i, PowerSeries.coeff 0 (c i) = 1) (i : ι) (k : ℕ) :
    eulerProduct (factors P c) ((P i : ℕ) ^ k) = PowerSeries.coeff k (c i) := by
  classical
  haveI := northcott_primes P hP
  have hev : ∀ᶠ s in atTop, (∏ j ∈ s, factors P c j) ((P i : ℕ) ^ k) =
      eulerProduct (factors P c) ((P i : ℕ) ^ k) :=
    tendsTo_eulerProduct_ofPowerSeries (fun i => (P i : ℕ)) c
      (fun i => by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hc i]) ((P i : ℕ) ^ k)
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 hev
  have hs := hs₀ (insert i s₀) (Finset.subset_insert i s₀)
  rw [← hs, ← Finset.insert_erase (Finset.mem_insert_self i s₀), Finset.prod_insert (Finset.notMem_erase i _)]
  have hp : (P i : ℕ).Prime := (P i).2
  have ht := prod_trivialAt hc hp ((insert i s₀).erase i) fun j hj hji =>
    (Finset.ne_of_mem_erase hj) (hP (Subtype.val_injective hji))
  rw [prime_pow_mul_apply hp _ _ ht]
  show ofPowerSeries (P i : ℕ) (c i) ((P i : ℕ) ^ k) = _
  exact ofPowerSeries_apply_pow hp.one_lt _ _

/-- Multiplicativity in the form used below: the value at `n ≠ 0` is the product over its prime factors. -/
theorem eulerProduct_factorization (hc : ∀ i, PowerSeries.coeff 0 (c i) = 1) {n : ℕ} (hn : n ≠ 0) :
    eulerProduct (factors P c) n = ∏ p ∈ n.primeFactors, eulerProduct (factors P c) (p ^ n.factorization p) := by
  rw [(isMultiplicative_eulerProduct_primes hc).multiplicative_factorization _ hn, Finsupp.prod,
    Nat.support_factorization]

/-! ## 3. The bound `|F n| ≤ d(n) √n` -/

/-- The square root of `n` is the product of the square roots of its prime-power parts. -/
theorem sqrt_eq_prod_primeFactors {n : ℕ} (hn : n ≠ 0) :
    Real.sqrt n = ∏ p ∈ n.primeFactors, Real.sqrt p ^ n.factorization p := by
  have h0 : 0 ≤ ∏ p ∈ n.primeFactors, Real.sqrt p ^ n.factorization p :=
    Finset.prod_nonneg fun _ _ => pow_nonneg (Real.sqrt_nonneg _) _
  rw [← Real.sqrt_mul_self h0, ← Finset.prod_mul_distrib]
  congr 1
  have : ∀ p ∈ n.primeFactors, Real.sqrt p ^ n.factorization p * Real.sqrt p ^ n.factorization p =
      ((p ^ n.factorization p : ℕ) : ℝ) := fun p _ => by
    rw [← mul_pow, Real.mul_self_sqrt (Nat.cast_nonneg _), Nat.cast_pow]
  rw [Finset.prod_congr rfl this, ← Nat.cast_prod]
  congr 1
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]

variable (P c) in
/-- The Hasse-type coefficient bound of `EulerProductBound`, at the primes `P i`. -/
def CoeffBound : Prop :=
  ∀ i k, |((PowerSeries.coeff k (c i) : ℤ) : ℝ)| ≤ max 1 ((k + 1) * Real.sqrt (P i : ℕ) ^ k)

/-- **`|F n| ≤ d(n) √n`.** -/
theorem abs_eulerProduct_le (hP : Function.Bijective P) (hc : ∀ i, PowerSeries.coeff 0 (c i) = 1)
    (hb : CoeffBound P c) {n : ℕ} (hn : n ≠ 0) :
    |((eulerProduct (factors P c) n : ℤ) : ℝ)| ≤ (n.divisors.card : ℝ) * Real.sqrt n := by
  rw [eulerProduct_factorization hc hn, Nat.card_divisors hn, sqrt_eq_prod_primeFactors hn]
  push_cast
  rw [Finset.abs_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  obtain ⟨i, hi⟩ := hP.2 ⟨p, hpp⟩
  have hpi : (P i : ℕ) = p := by rw [hi]
  set k := n.factorization p
  rw [← hpi, eulerProduct_prime_pow hP.1 hc i k]
  refine (hb i k).trans (max_le ?_ le_rfl)
  rw [hpi]
  have h1 : (1 : ℝ) ≤ k + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have h2 : (1 : ℝ) ≤ Real.sqrt p ^ k :=
    one_le_pow₀ (Real.one_le_sqrt.2 (by exact_mod_cast hpp.one_lt.le))
  nlinarith

/-! ## 4. Summability -/

/-- The divisor-counting function has a summable L-series for `re s > 1` (it is `ζ * ζ`). -/
theorem lseriesSummable_card_divisors {t : ℂ} (ht : 1 < t.re) :
    LSeriesSummable (fun n => ((n.divisors.card : ℕ) : ℂ)) t := by
  have hm := ArithmeticFunction.LSeriesSummable_mul (f := (ζ : ArithmeticFunction ℂ)) (g := (ζ : ArithmeticFunction ℂ))
    (LSeriesSummable_zeta_iff.mpr ht) (LSeriesSummable_zeta_iff.mpr ht)
  have key : (ζ * ζ : ArithmeticFunction ℕ) = σ 0 := by
    rw [← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]
  rw [← natCoe_mul, key] at hm
  have hfun : (fun n : ℕ => ((n.divisors.card : ℕ) : ℂ)) = ↗((σ 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) := by
    funext n; simp [sigma_zero_apply]
  rw [hfun]
  exact hm

/-- **The bound gives absolute convergence for `re s > 3/2`.** -/
theorem lseriesSummable_eulerProduct_primes (hP : Function.Bijective P) (hc : ∀ i, PowerSeries.coeff 0 (c i) = 1)
    (hb : CoeffBound P c) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable (fun n => ((eulerProduct (factors P c) n : ℤ) : ℂ)) s := by
  set t : ℂ := s - ((1 / 2 : ℝ) : ℂ) with htdef
  have ht : 1 < t.re := by simp only [htdef, Complex.sub_re, Complex.ofReal_re]; linarith
  have hG := (summable_norm_iff (E := ℂ)).2 (lseriesSummable_card_divisors ht)
  refine Summable.of_norm_bounded hG fun n => ?_
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [hn, ↓reduceIte, Complex.norm_natCast]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hre : s.re = t.re + 1 / 2 := by simp only [htdef, Complex.sub_re, Complex.ofReal_re]; ring
  rw [hre, Real.rpow_add hnpos, Complex.norm_intCast]
  have hsq : Real.sqrt n = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow n
  have hb' := abs_eulerProduct_le hP hc hb hn
  rw [hsq] at hb'
  have hpos1 : 0 < (n : ℝ) ^ t.re := Real.rpow_pos_of_pos hnpos _
  have hpos2 : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hnpos _
  rw [div_le_div_iff₀ (mul_pos hpos1 hpos2) hpos1]
  calc |((eulerProduct (factors P c) n : ℤ) : ℝ)| * (n : ℝ) ^ t.re
      ≤ ((n.divisors.card : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) * (n : ℝ) ^ t.re :=
        mul_le_mul_of_nonneg_right hb' hpos1.le
    _ = (n.divisors.card : ℝ) * ((n : ℝ) ^ t.re * (n : ℝ) ^ (1 / 2 : ℝ)) := by ring

/-! ## 5. Over `ℚ` -/

section Rat

open Rat.HeightOneSpectrum

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- **At a prime `v` of `𝓞 ℚ` the residue field of the completion has `p_v` elements.** -/
theorem card_residueField_rat (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = (primesEquiv v : ℕ) := by
  have e : IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) ≃+* ZMod (primesEquiv v : ℕ) :=
    (IsLocalRing.ResidueField.mapEquiv (adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      (PadicInt.residueField (p := (primesEquiv v : ℕ)))
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod]

/-- **The Euler product bound over `ℚ`** (no longer named for curves over `ℚ`). -/
theorem eulerProductBound_rat : EulerProductBound ℚ := by
  intro c hc0 hb s hs
  simp only [card_residueField_rat] at hb ⊢
  exact lseriesSummable_eulerProduct_primes (P := primesEquiv) primesEquiv.bijective hc0 hb hs

/-- **Hasse gives absolute convergence for `re s > 3/2`**, over `ℚ`, with nothing else named. -/
theorem LSeriesSummable_of_hasse_rat (W : WeierstrassCurve ℚ) (hH : R136a1 "Hasse" (Hasse W)) {s : ℂ}
    (hs : 3 / 2 < s.re) : LSeriesSummable (lcoeff W) s :=
  LSeriesSummable_of_hasse W hH eulerProductBound_rat hs

/-- **Hasse gives a finite order at `s = 1`**, over `ℚ`, with nothing else named. -/
theorem order_ne_top_rat {W : WeierstrassCurve ℚ} {Lam : ℂ → ℂ} (hL : IsContinuation W Lam)
    (hH : R136a1 "Hasse" (Hasse W)) : analyticOrderAt Lam 1 ≠ ⊤ :=
  order_ne_top hL hH eulerProductBound_rat

/-- **Parity of the analytic rank**, over `ℚ`, from `Hasse` and the functional equation. -/
theorem analytic_parity_of_hasse_rat {W : WeierstrassCurve ℚ} {Lam : ℂ → ℂ} (hL : IsContinuation W Lam) {w : ℂ}
    (hfe : FunctionalEquation ℚ Lam w) (hH : R136a1 "Hasse" (Hasse W)) :
    w = (-1) ^ (analyticOrderAt Lam 1).toNat :=
  analytic_parity_of_hasse hL hfe hH eulerProductBound_rat

end Rat

end Arsenal.BSD
