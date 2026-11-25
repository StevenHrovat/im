/-
The full turn: a quantity read off by going once around a point and averaging.
Released under the Apache License 2.0.
-/
import Mathlib

/-!
# The full turn

Go once around a point, from `-π` to `+π`, and average: the `+` half mirrors the `-` half, and one exact number is left. Two forms,
one statement.

**Discrete** (one turn in `N` equal steps, the `N`-th roots of unity).
* `full_turn`: the powers `ζ ^ (j * k)` of a primitive `N`-th root of unity, summed over one turn `j < N`, give `N` when `N ∣ k`
  and `0` otherwise.
* `full_turn_cos`: the same in real numbers, `∑_{j < N} cos (2π j k / N)`.
* `full_turn_coeff`: one turn reads off any coefficient of a sum of `N` powers (coefficient extraction).

**Continuous** (one turn around a circle).
* `full_turn_circle`: one turn around `c` reads off the `n`-th Taylor coefficient of a function holomorphic on the disc
  (Cauchy's formula for derivatives, from Mathlib).
* `full_turn_factorial`: `1 / n!` is one turn of `exp z / z ^ (n + 1)` around `0`, on a circle of any radius. The factorial is
  a full turn.
* `full_turn_leading`: if `Λ = (s - c) ^ r g`, one turn of `Λ / (s - c) ^ (r + 1)` gives `g c`, the leading coefficient.
* `full_turn_order`: one turn of the logarithmic derivative of `(s - c) ^ r g` (with `g` nowhere zero) gives `r`: the order of a
  zero is a winding number. For an L-function at `s = 1` these are the BSD leading coefficient and the analytic rank.

**The balance** (what one turn forbids).
* `full_turn_balance`: a positive function on `N ≥ 2` points and its positive full-turn transform cannot both be flat: some
  nontrivial value of one of them is at most `1 / (1 + √N)` of its value at the base point. The two linear identities the turn
  gives (`hsum`, `hbase`) are all it uses.
* `full_turn_balance_log`: the same as free energies, `log (1 + √N) ≤ log (z o / z k)` or `≤ log (ε o' / ε e)`. For `N = 2` this
  is the hand-over rate `log (1 + √2)` of the twist and electric free energies.

Mathlib alone, nothing open.
-/

open Complex Finset

namespace Arsenal.FullTurn

/-! ## The discrete full turn -/

/-- **The discrete full turn**: summing the powers `ζ ^ (j * k)` of a primitive `N`-th root of unity over one turn `j < N` gives
`N` when `N ∣ k` and `0` otherwise. -/
theorem full_turn {K : Type*} [Field K] {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (k : ℕ) :
    ∑ j ∈ range N, ζ ^ (j * k) = if N ∣ k then (N : K) else 0 := by
  have hpow : ∀ j, ζ ^ (j * k) = (ζ ^ k) ^ j := fun j => by rw [← pow_mul, mul_comm]
  simp_rw [hpow]
  split_ifs with h
  · have h1 : ζ ^ k = 1 := (hζ.pow_eq_one_iff_dvd k).2 h
    simp [h1]
  · have hne : ζ ^ k ≠ 1 := fun h1 => h ((hζ.pow_eq_one_iff_dvd k).1 h1)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

/-- **The discrete full turn in real numbers**: `∑_{j < N} cos (2π j k / N)` is `N` when `N ∣ k` and `0` otherwise. -/
theorem full_turn_cos {N : ℕ} (hN : 0 < N) (k : ℕ) :
    ∑ j ∈ range N, Real.cos (2 * Real.pi * j * k / N) = if N ∣ k then (N : ℝ) else 0 := by
  have hζ : IsPrimitiveRoot (exp (2 * Real.pi * I / N)) N := isPrimitiveRoot_exp N (by omega)
  have hre := congrArg Complex.re (full_turn hζ k)
  have hterm : ∀ j : ℕ, (exp (2 * Real.pi * I / N) ^ (j * k)).re = Real.cos (2 * Real.pi * j * k / N) := by
    intro j
    rw [← Complex.exp_nat_mul]
    have h : ((j * k : ℕ) : ℂ) * (2 * Real.pi * I / N) = ((2 * Real.pi * j * k / N : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [h, exp_ofReal_mul_I_re]
  rw [re_sum] at hre
  simp_rw [hterm] at hre
  rw [hre]
  split_ifs <;> simp

private lemma dvd_shift {N m k : ℕ} (hm : m < N) (hk : k < N) : N ∣ m + (N - k) ↔ m = k := by
  constructor
  · rintro ⟨q, hq⟩
    have hq1 : q = 1 := by
      rcases Nat.lt_or_ge q 1 with h | h
      · interval_cases q; omega
      · rcases Nat.lt_or_ge q 2 with h' | h'
        · omega
        · have := Nat.mul_le_mul_left N h'; omega
    subst hq1; omega
  · rintro rfl; exact ⟨1, by omega⟩

/-- **Coefficient extraction by one turn**: for `p = ∑_{m < N} c m ζ ^ m` read at the `N` points `ζ ^ j`, the average of
`p (ζ ^ j) ζ ^ (j (N - k))` over one turn is the coefficient `c k`. -/
theorem full_turn_coeff {K : Type*} [Field K] [CharZero K] {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (c : ℕ → K)
    {k : ℕ} (hk : k < N) :
    (N : K)⁻¹ * ∑ j ∈ range N, (∑ m ∈ range N, c m * ζ ^ (j * m)) * ζ ^ (j * (N - k)) = c k := by
  have hN : (N : K) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hswap : ∑ j ∈ range N, (∑ m ∈ range N, c m * ζ ^ (j * m)) * ζ ^ (j * (N - k))
      = ∑ m ∈ range N, c m * ∑ j ∈ range N, ζ ^ (j * (m + (N - k))) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_add, pow_add, mul_assoc]
  rw [hswap]
  simp_rw [full_turn hζ]
  rw [Finset.sum_eq_single k]
  · simp only [show N ∣ k + (N - k) from ⟨1, by omega⟩, ↓reduceIte]; field_simp
  · intro m hm hmk
    simp only [show ¬ N ∣ m + (N - k) from fun h => hmk ((dvd_shift (Finset.mem_range.1 hm) hk).1 h), ↓reduceIte, mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 hk) h

/-! ## The continuous full turn -/

/-- **The continuous full turn**: one turn around `c` on a circle of radius `R > 0` reads off the `n`-th Taylor coefficient of a
function continuous on the closed disc and holomorphic inside (Cauchy's formula for derivatives). -/
theorem full_turn_circle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {c : ℂ}
    {R : ℝ} (hR : 0 < R) (n : ℕ) (hc : ContinuousOn f (Metric.closedBall c R))
    (hd : ∀ z ∈ Metric.ball c R, DifferentiableAt ℂ f z) :
    (2 * Real.pi * I)⁻¹ • ∮ z in C(c, R), (1 / (z - c) ^ (n + 1)) • f z
      = ((n.factorial : ℂ)⁻¹) • iteratedDeriv n f c := by
  rw [circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable hR n Set.countable_empty hc
    (fun z hz => hd z hz.1), smul_smul]
  congr 1
  have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := two_pi_I_ne_zero
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- **The factorial is a full turn**: `1 / n!` is one turn of `exp z / z ^ (n + 1)` around `0`, on a circle of any radius
`R > 0` (at `R = n` the first-order oscillation cancels, and the Gaussian part of the turn is Stirling's `√(2πn)`). -/
theorem full_turn_factorial (n : ℕ) {R : ℝ} (hR : 0 < R) :
    (2 * Real.pi * I)⁻¹ * ∮ z in C(0, R), (z ^ (n + 1))⁻¹ * exp z = ((n.factorial : ℂ))⁻¹ := by
  have h := full_turn_circle (f := exp) (c := 0) hR n continuous_exp.continuousOn
    (fun z _ => differentiableAt_exp)
  have hd : iteratedDeriv n exp 0 = 1 := by
    have hfun : (exp : ℂ → ℂ) = fun s => exp (1 * s) := by funext s; rw [one_mul]
    rw [hfun, iteratedDeriv_cexp_const_mul]
    simp
  simp only [sub_zero, one_div, smul_eq_mul, hd, mul_one] at h
  exact h

/-- **The leading coefficient is one turn**: if `Λ = (s - c) ^ r g` on the circle and `g` is holomorphic on the disc, one turn of
`Λ / (s - c) ^ (r + 1)` around `c` gives `g c`, the leading coefficient of `Λ` at `c` (for an L-function at `s = 1` with
`r` the order of the zero: the BSD leading coefficient, with the `r!` of `Λ^(r)(1) / r!` taken up by the turn). -/
theorem full_turn_leading {Λ g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) (r : ℕ)
    (hΛ : ∀ z ∈ Metric.sphere c R, Λ z = (z - c) ^ r * g z)
    (hc : ContinuousOn g (Metric.closedBall c R)) (hd : ∀ z ∈ Metric.ball c R, DifferentiableAt ℂ g z) :
    (2 * Real.pi * I)⁻¹ * ∮ z in C(c, R), ((z - c) ^ (r + 1))⁻¹ * Λ z = g c := by
  have h := full_turn_circle hR 0 hc hd
  simp only [zero_add, pow_one, one_div, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, inv_one,
    smul_eq_mul, one_mul] at h
  rw [← h]
  congr 1
  apply circleIntegral.integral_congr hR.le
  intro z hz
  have hzc : z - c ≠ 0 := by
    intro h0
    rw [Metric.mem_sphere, dist_eq_norm, h0, norm_zero] at hz
    linarith
  simp only [hΛ z hz]
  field_simp
  ring

/-- **The order is a winding number**: if `g` is holomorphic and nowhere zero on a disc of radius `R' > R`, one turn of the
logarithmic derivative of `(s - c) ^ r g` around `c` gives `r` (the argument principle for one zero of order `r`: for an
L-function at `s = 1`, the analytic rank). -/
theorem full_turn_order {g : ℂ → ℂ} {c : ℂ} {R R' : ℝ} (hR : 0 < R) (hRR : R < R') (r : ℕ)
    (hg : DifferentiableOn ℂ g (Metric.ball c R')) (hg0 : ∀ z ∈ Metric.ball c R', g z ≠ 0) :
    (2 * Real.pi * I)⁻¹ * ∮ z in C(c, R), deriv (fun s => (s - c) ^ r * g s) z / ((z - c) ^ r * g z) = r := by
  have hopen : IsOpen (Metric.ball c R') := Metric.isOpen_ball
  have hsub : Metric.closedBall c R ⊆ Metric.ball c R' := Metric.closedBall_subset_ball hRR
  have hdg : ∀ z ∈ Metric.ball c R', HasDerivAt g (deriv g z) z :=
    fun z hz => ((hg z hz).differentiableAt (hopen.mem_nhds hz)).hasDerivAt
  have hg' : DifferentiableOn ℂ (deriv g) (Metric.ball c R') := hg.deriv hopen
  -- on the circle the logarithmic derivative splits into r / (z - c) and g' / g
  have hsplit : Set.EqOn (fun z => deriv (fun s => (s - c) ^ r * g s) z / ((z - c) ^ r * g z))
      (fun z => (r : ℂ) * (z - c)⁻¹ + deriv g z / g z) (Metric.sphere c R) := by
    intro z hz
    have hzR : z ∈ Metric.ball c R' := hsub (Metric.sphere_subset_closedBall hz)
    have hzc : z - c ≠ 0 := by
      intro h0
      rw [Metric.mem_sphere, dist_eq_norm, h0, norm_zero] at hz
      linarith
    have hgz := hg0 z hzR
    have hd : HasDerivAt (fun s => (s - c) ^ r * g s)
        ((r : ℂ) * (z - c) ^ (r - 1) * 1 * g z + (z - c) ^ r * deriv g z) z := by
      convert (((hasDerivAt_id z).sub_const c).pow r).mul (hdg z hzR) using 1
      · funext s; simp
      · simp
    dsimp only
    rw [hd.deriv]
    rcases r with _ | m
    · simp
    · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
  rw [circleIntegral.integral_congr hR.le hsplit]
  have hint1 : CircleIntegrable (fun z => (r : ℂ) * (z - c)⁻¹) c R :=
    (ContinuousOn.mul continuousOn_const ((continuousOn_id.sub continuousOn_const).inv₀ (fun z hz h0 => by
      have h0' : z - c = 0 := by simpa using h0
      rw [Metric.mem_sphere, dist_eq_norm, h0', norm_zero] at hz; linarith))).circleIntegrable hR.le
  have hcont2 : ContinuousOn (fun z => deriv g z / g z) (Metric.closedBall c R) :=
    (hg'.continuousOn.mono hsub).div (hg.continuousOn.mono hsub) (fun z hz => hg0 z (hsub hz))
  have hint2 : CircleIntegrable (fun z => deriv g z / g z) c R :=
    (hcont2.mono Metric.sphere_subset_closedBall).circleIntegrable hR.le
  rw [circleIntegral.integral_add hint1 hint2, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_inv_of_mem_ball (Metric.mem_ball_self hR)]
  have hzero : ∮ z in C(c, R), deriv g z / g z = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le Set.countable_empty hcont2
      (fun z hz => ((hg'.div hg (fun w hw => hg0 w hw)) z (Metric.ball_subset_ball hRR.le hz.1)).differentiableAt
        (hopen.mem_nhds (Metric.ball_subset_ball hRR.le hz.1)))
  rw [hzero, add_zero]
  have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := two_pi_I_ne_zero
  field_simp

/-! ## The balance -/

/-- **The full-turn balance**: let `z` be positive on `N ≥ 2` points `ι` and `ε` positive on `N` points `κ`, tied by the two
identities one turn gives: the values of `ε` add up to `z o`, and `N ε o'` is the sum of the values of `z`. Then some nontrivial
value of `z` or of `ε` is at most `1 / (1 + √N)` of its base value. -/
theorem full_turn_balance {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {N : ℕ}
    (hι : Fintype.card ι = N) (hκ : Fintype.card κ = N) (hN : 2 ≤ N) (o : ι) (o' : κ) (z : ι → ℝ) (ε : κ → ℝ)
    (hz : ∀ k, 0 < z k) (hε : ∀ e, 0 < ε e) (hsum : ∑ e, ε e = z o) (hbase : (N : ℝ) * ε o' = ∑ k, z k) :
    (∃ k, k ≠ o ∧ (1 + √(N : ℝ)) * z k ≤ z o) ∨ (∃ e, e ≠ o' ∧ (1 + √(N : ℝ)) * ε e ≤ ε o') := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hzk, hεe⟩ := hcon
  set s := √(N : ℝ) with hs
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs0 : 0 < s := Real.sqrt_pos.2 hNpos
  have hss : s * s = N := Real.mul_self_sqrt hNpos.le
  set T := (Finset.univ : Finset ι).erase o
  set U := (Finset.univ : Finset κ).erase o'
  have hT : T.card = N - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ o), Finset.card_univ, hι]
  have hU : U.card = N - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ o'), Finset.card_univ, hκ]
  have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
  have hUne : U.Nonempty := Finset.card_pos.1 (by omega)
  have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by push_cast [Nat.cast_sub (show 1 ≤ N by omega)]; ring
  -- every nontrivial value is more than 1/(1+s) of its base value; add them up
  have h1 : ((N : ℝ) - 1) * z o < (1 + s) * ∑ k ∈ T, z k := by
    have := Finset.sum_lt_sum_of_nonempty hTne (fun k hk => hzk k (Finset.ne_of_mem_erase hk))
    rw [Finset.sum_const, hT, nsmul_eq_mul, hN1, ← Finset.mul_sum] at this
    exact this
  have h2 : ((N : ℝ) - 1) * ε o' < (1 + s) * ∑ e ∈ U, ε e := by
    have := Finset.sum_lt_sum_of_nonempty hUne (fun e he => hεe e (Finset.ne_of_mem_erase he))
    rw [Finset.sum_const, hU, nsmul_eq_mul, hN1, ← Finset.mul_sum] at this
    exact this
  have hz_split : ∑ k, z k = z o + ∑ k ∈ T, z k := (Finset.add_sum_erase _ _ (Finset.mem_univ o)).symm
  have hε_split : ∑ e, ε e = ε o' + ∑ e ∈ U, ε e := (Finset.add_sum_erase _ _ (Finset.mem_univ o')).symm
  set S := ∑ k ∈ T, z k
  set W := ∑ e ∈ U, ε e
  have hW : W = z o - ε o' := by linarith
  rw [hW] at h2
  have hzo := hz o
  have hεo := hε o'
  -- (N + s) ε o' < (1 + s) z o, so (N + s)(z o + S) < N (1 + s) z o
  have hA : ((N : ℝ) + s) * ε o' < (1 + s) * z o := by nlinarith
  have hB : ((N : ℝ) + s) * (z o + S) < (N : ℝ) * (1 + s) * z o := by
    have : z o + S = (N : ℝ) * ε o' := by rw [hbase, hz_split]
    rw [this]; nlinarith
  -- and (1 + s)(z o + S) > (N + s) z o, while N (1 + s)^2 = (N + s)^2
  have hC : ((N : ℝ) + s) * z o < (1 + s) * (z o + S) := by nlinarith
  have hD : ((N : ℝ) + s) * ((N : ℝ) + s) * z o < ((N : ℝ) + s) * ((1 + s) * (z o + S)) :=
    by have hp : (0 : ℝ) < N + s := by linarith
       nlinarith [mul_lt_mul_of_pos_left hC hp]
  have hE : ((N : ℝ) + s) * (z o + S) * (1 + s) < (N : ℝ) * (1 + s) * z o * (1 + s) :=
    mul_lt_mul_of_pos_right hB (by linarith)
  nlinarith [hss]

/-- **The full-turn balance as free energies**: under the hypotheses of `full_turn_balance`, `log (1 + √N)` is at most the free
energy `log (z o / z k)` of some nontrivial `k`, or `log (ε o' / ε e)` of some nontrivial `e`. -/
theorem full_turn_balance_log {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {N : ℕ}
    (hι : Fintype.card ι = N) (hκ : Fintype.card κ = N) (hN : 2 ≤ N) (o : ι) (o' : κ) (z : ι → ℝ) (ε : κ → ℝ)
    (hz : ∀ k, 0 < z k) (hε : ∀ e, 0 < ε e) (hsum : ∑ e, ε e = z o) (hbase : (N : ℝ) * ε o' = ∑ k, z k) :
    (∃ k, k ≠ o ∧ Real.log (1 + √(N : ℝ)) ≤ Real.log (z o / z k)) ∨
      (∃ e, e ≠ o' ∧ Real.log (1 + √(N : ℝ)) ≤ Real.log (ε o' / ε e)) := by
  have hpos : 0 < 1 + √(N : ℝ) := by positivity
  rcases full_turn_balance hι hκ hN o o' z ε hz hε hsum hbase with ⟨k, hk, h⟩ | ⟨e, he, h⟩
  · exact Or.inl ⟨k, hk, Real.log_le_log hpos ((le_div_iff₀ (hz k)).2 h)⟩
  · exact Or.inr ⟨e, he, Real.log_le_log hpos ((le_div_iff₀ (hε e)).2 h)⟩

end Arsenal.FullTurn
