/-
The generalized Riemann hypothesis: the Mathlib-only core, in native IM form.
Released under the Apache License 2.0.

The claim of A. M. Masullo's draft *The Music of the Primes* (GRH for the Hecke L-functions of every number field), stated
from Mathlib alone, with the one open step of its route answered R136a1. Imports Mathlib and the arsenal only; nothing is
taken from a formalization of the Riemann hypothesis or derived from one.
-/
import Mathlib
import Arsenal.R136a1

/-!
# GRH: what Mathlib alone gives, and the one open step of Masullo's route

**The statement about the coefficients alone.** An L-series is given by its coefficients `a : ℕ → ℂ`. A *continuation*
of it (`Continues a f`) is a function differentiable on `ℂ` minus the pole at `1` that equals the series where it
converges (`re s > 1`). `SeriesGRH a` says: every continuation has all its zeros in the open critical strip on the line
`re s = 1/2`. There is at most one continuation (`Continues.eqOn`), so `SeriesGRH a` is the statement about the one
continuation when it exists (`grh_iff`); it reads `a` alone and depends on no chosen function.

**The family.** Mathlib v4.34.0 defines the Riemann zeta function, the L-functions of Dirichlet characters, both
continued, and the Dedekind zeta function of a number field as a series (not continued). It does not define Hecke
characters. So:
* the zeta function and every Dirichlet L-function are proved to be continuations here (`continues_zeta`,
  `continues_dirichlet`);
* the Dedekind zeta function enters by its coefficients (`dedekindCoeff`), and `DedekindGRH K` is `SeriesGRH` of them;
* the Hecke family enters as a set of coefficient sequences that contains every Dirichlet character (`HeckeFamily`):
  whoever builds Hecke characters supplies it and proves that one field.

**The ladder, proved.** Hecke GRH gives GRH for every Dirichlet L-function (`dirichlet_of_hecke`), which gives the Riemann
hypothesis in Mathlib's own words (`riemannHypothesis_of_dirichlet`, through the modulus `1`). The step from zeros in the
strip to Mathlib's `RiemannHypothesis` is an equivalence (`riemannHypothesis_iff_onLine`): nonvanishing on `re s ≥ 1`
and the functional equation leave only the trivial zeros outside the strip.

**Masullo's route and its one open step.** The route runs through a trace formula. Its formalization (the project
`riemann-masullo`, the declaration `traceFormula_exteriorZeros`) rests every target on one unproved statement: the zeros
outside the band `|re s - 1/2| < α` cancel, for every width `α > 0`. Read at the zeros (the form that project proved
equivalent to it), that is the gap `Gap f α`: no zero in the strip at distance `α` or more from the line. Here:
* the route, with its open step answered R136a1, gives GRH (`grh_of_masullo`);
* the widths `α ≥ 1/2` hold for free (`gap_of_half_le`);
* **the open step is GRH itself** (`masullo_gap_iff_grh`): the gap at every width is equivalent to the conclusion. As a
  card, the route moves the whole claim into its one open step; the open step carries all of it.
  The formalization proved this first, at the level of the trace formula and over every number field
  (`introTrace_exterior_cancellation_iff_all_zeros_in_window`, `introTrace_cofinal_exterior_cancellation_iff_critical_line`);
  here it is restated at the zeros.

This module proves nothing that is open. Standard axioms only.
-/

namespace Arsenal.GRH

open Complex
open scoped Real

/-- **The open critical strip** `0 < re s < 1`. -/
def Strip : Set ℂ := {s | 0 < s.re ∧ s.re < 1}

/-- **The zeros of `f` in the critical strip lie on the line** `re s = 1/2`. -/
def OnLine (f : ℂ → ℂ) : Prop := ∀ s ∈ Strip, f s = 0 → s.re = 1 / 2

/-- **`f` continues the L-series of `a`**: differentiable on `ℂ` minus the pole at `1`, and equal to the series on
`re s > 1`, where it converges. -/
structure Continues (a : ℕ → ℂ) (f : ℂ → ℂ) : Prop where
  differentiableOn : DifferentiableOn ℂ f {1}ᶜ
  eq_series : ∀ s : ℂ, 1 < s.re → f s = LSeries a s

/-- **GRH for the L-series of `a`**: every continuation has its zeros in the critical strip on the line. -/
def SeriesGRH (a : ℕ → ℂ) : Prop := ∀ f, Continues a f → OnLine f

/-- **There is at most one continuation**: two continuations agree everywhere off the pole (identity theorem on the
connected set `ℂ \ {1}`, from agreement near `s = 2`). -/
theorem Continues.eqOn {a : ℕ → ℂ} {f g : ℂ → ℂ} (hf : Continues a f) (hg : Continues a g) :
    Set.EqOn f g {1}ᶜ := by
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hf.differentiableOn.analyticOnNhd isOpen_compl_singleton)
    (hg.differentiableOn.analyticOnNhd isOpen_compl_singleton) hpc h2 ?_
  have hU : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
  filter_upwards [hU] with z hz
  rw [hf.eq_series z hz, hg.eq_series z hz]

/-- **GRH is a statement about the one continuation**: with a continuation in hand, it is that its zeros in the strip
lie on the line. -/
theorem grh_iff {a : ℕ → ℂ} {f : ℂ → ℂ} (hf : Continues a f) : SeriesGRH a ↔ OnLine f := by
  refine ⟨fun h => h f hf, fun h g hg s hs hgs => h s hs ?_⟩
  have hs1 : s ∈ ({1}ᶜ : Set ℂ) := fun e => by
    rw [Set.mem_singleton_iff] at e
    have := hs.2
    rw [e, one_re] at this
    exact lt_irrefl _ this
  rw [hf.eqOn hg hs1]
  exact hgs

/-! ## The family: zeta, Dirichlet, Dedekind, Hecke -/

/-- **The Riemann zeta function continues the series of the constant `1`.** -/
theorem continues_zeta : Continues 1 riemannZeta where
  differentiableOn := fun _ hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  eq_series := fun _ hs => (LSeries_one_eq_riemannZeta hs).symm

/-- **The L-function of a Dirichlet character continues its series.** -/
theorem continues_dirichlet {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Continues (fun n => χ n) (DirichletCharacter.LFunction χ) where
  differentiableOn := fun s hs =>
    (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
  eq_series := fun _ hs => DirichletCharacter.LFunction_eq_LSeries χ hs

/-- **GRH for the Dirichlet L-functions of modulus `N`**, in Mathlib's functions. -/
def DirichletGRH (N : ℕ) [NeZero N] : Prop :=
  ∀ χ : DirichletCharacter ℂ N, OnLine (DirichletCharacter.LFunction χ)

/-- Dirichlet GRH is GRH of the characters' coefficients. -/
theorem dirichletGRH_iff (N : ℕ) [NeZero N] :
    DirichletGRH N ↔ ∀ χ : DirichletCharacter ℂ N, SeriesGRH (fun n => χ n) :=
  forall_congr' fun χ => (grh_iff (continues_dirichlet χ)).symm

/-- **The coefficients of the Dedekind zeta function** of `K`: the number of ideals of `𝓞 K` of norm `n`, the
coefficients of Mathlib's `NumberField.dedekindZeta`. -/
noncomputable def dedekindCoeff (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℂ :=
  Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n}

/-- Mathlib's Dedekind zeta function is the series of these coefficients. -/
theorem dedekindZeta_eq (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    NumberField.dedekindZeta K s = LSeries (dedekindCoeff K) s := rfl

/-- **GRH for the Dedekind zeta function of `K`**, a statement about its coefficients. Mathlib v4.34.0 does not continue
the Dedekind zeta function; a continuation, once built, turns this into its zeros on the line (`grh_iff`). -/
def DedekindGRH (K : Type*) [Field K] [NumberField K] : Prop := SeriesGRH (dedekindCoeff K)

/-- **The Hecke family**: the coefficient sequences of the L-functions of the unitary Hecke characters of every number
field. Mathlib v4.34.0 has no Hecke characters, so the family is supplied by whoever builds them, with the one fact the
ladder needs: every Dirichlet character is a Hecke character (over `ℚ`). -/
structure HeckeFamily where
  coeffs : Set (ℕ → ℂ)
  dirichlet_mem : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), (fun n : ℕ => χ n) ∈ coeffs

/-- **Masullo's claim**: GRH for every L-function of the Hecke family. -/
def HeckeGRH (H : HeckeFamily) : Prop := ∀ a ∈ H.coeffs, SeriesGRH a

/-! ## The ladder: Hecke, Dirichlet, Riemann -/

/-- **Hecke GRH gives Dirichlet GRH**, at every modulus. -/
theorem dirichlet_of_hecke {H : HeckeFamily} (h : HeckeGRH H) (N : ℕ) [NeZero N] : DirichletGRH N :=
  (dirichletGRH_iff N).2 fun χ => h _ (H.dirichlet_mem N χ)

/-- The trivial character of modulus `1` has the Riemann zeta function as its L-function. -/
theorem onLine_zeta_of_dirichlet (h : DirichletGRH 1) : OnLine riemannZeta := by
  have := h 1
  rwa [DirichletCharacter.LFunction_modOne_eq] at this

/-- A zero of `ζ` with `re s ≤ 0` is a trivial zero. -/
theorem trivial_of_re_nonpos {s : ℂ} (hz : riemannZeta s = 0) (hs : s.re ≤ 0) :
    ∃ n : ℕ, s = -2 * (n + 1) := by
  obtain ⟨t, rfl⟩ : ∃ t : ℂ, s = 1 - t := ⟨1 - s, by ring⟩
  have hre : 1 ≤ t.re := by rw [sub_re, one_re] at hs; linarith
  have ht0 : ∀ n : ℕ, t ≠ -n := fun n e => by
    have := congrArg re e
    rw [neg_re, natCast_re] at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs0 : 1 - t ≠ 0 := fun e => by
    rw [e, riemannZeta_zero] at hz
    norm_num at hz
  have ht1 : t ≠ 1 := fun e => hs0 (by rw [e]; ring)
  have hfe := riemannZeta_one_sub ht0 ht1
  rw [hz] at hfe
  have hζ : riemannZeta t ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre
  have hΓ : Gamma t ≠ 0 := Gamma_ne_zero ht0
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hpow : (2 * (π : ℂ)) ^ (-t) ≠ 0 := cpow_ne_zero_iff.2 (Or.inl (mul_ne_zero two_ne_zero hπ))
  have hcos : cos (π * t / 2) = 0 := by
    have h0 := hfe.symm
    simp only [mul_eq_zero, two_ne_zero, hpow, hΓ, hζ, false_or, or_false] at h0
    exact h0
  obtain ⟨k, hk⟩ := cos_eq_zero_iff.1 hcos
  have htk : t = 2 * k + 1 := by
    have h' : (t - (2 * k + 1)) * π = 0 := by linear_combination 2 * hk
    rcases mul_eq_zero.1 h' with h | h
    · linear_combination h
    · exact absurd h hπ
  have hsk : 1 - t = -2 * k := by rw [htk]; ring
  -- `t = 2k + 1` with `re t ≥ 1` and `t ≠ 1`, so `k ≥ 1`.
  have hk1 : 1 ≤ k := by
    have hr := congrArg re htk
    simp only [add_re, mul_re, re_ofNat, intCast_re, im_ofNat, intCast_im, mul_zero, sub_zero, one_re] at hr
    have : (0 : ℝ) ≤ k := by linarith
    have hk0 : k ≠ 0 := fun e => ht1 (by rw [htk, e]; simp)
    have : 0 ≤ k := by exact_mod_cast this
    omega
  refine ⟨(k - 1).toNat, ?_⟩
  rw [hsk]
  have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
  have hc : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by exact_mod_cast this
  rw [hc]
  ring

/-- **The Riemann hypothesis is the zeros of `ζ` in the strip on the line**: Mathlib's `RiemannHypothesis` read on the
strip. Outside it, `re s ≥ 1` has no zeros and `re s ≤ 0` only the trivial ones. -/
theorem riemannHypothesis_iff_onLine : RiemannHypothesis ↔ OnLine riemannZeta := by
  constructor
  · intro h s hs hz
    refine h s hz ?_ ?_
    · rintro ⟨n, rfl⟩
      have := hs.1
      simp only [neg_mul, neg_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, add_re, natCast_re, one_re] at this
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · rintro rfl
      exact absurd hs.2 (by simp)
  · intro h s hz htriv _
    rcases le_or_gt s.re 0 with h0 | h0
    · exact absurd (trivial_of_re_nonpos hz h0) htriv
    rcases lt_or_ge s.re 1 with h1 | h1
    · exact h s ⟨h0, h1⟩ hz
    · exact absurd hz (riemannZeta_ne_zero_of_one_le_re h1)

/-- **Dirichlet GRH at modulus `1` gives the Riemann hypothesis**, in Mathlib's words. -/
theorem riemannHypothesis_of_dirichlet (h : DirichletGRH 1) : RiemannHypothesis :=
  riemannHypothesis_iff_onLine.2 (onLine_zeta_of_dirichlet h)

/-- **Masullo's claim gives the Riemann hypothesis.** -/
theorem riemannHypothesis_of_hecke {H : HeckeFamily} (h : HeckeGRH H) : RiemannHypothesis :=
  riemannHypothesis_of_dirichlet (dirichlet_of_hecke h 1)

/-! ## Masullo's route: the gap, its one open step, and why it is the claim -/

/-- **The gap at width `α`**: no zero of `f` in the critical strip at distance `α` or more from the line. The open step
of Masullo's route (the exterior zeros of the trace formula cancel), read at the zeros. -/
def Gap (f : ℂ → ℂ) (α : ℝ) : Prop := ∀ s ∈ Strip, f s = 0 → |s.re - 1 / 2| < α

/-- **The widths `α ≥ 1/2` hold for free**: every point of the open strip is within `1/2` of the line. -/
theorem gap_of_half_le (f : ℂ → ℂ) {α : ℝ} (hα : 1 / 2 ≤ α) : Gap f α := fun s hs _ => by
  rw [abs_lt]
  constructor <;> linarith [hs.1, hs.2]

/-- **The gap at every width is the line.** -/
theorem onLine_iff_gap (f : ℂ → ℂ) : OnLine f ↔ ∀ α : ℝ, 0 < α → Gap f α := by
  constructor
  · intro h α hα s hs hz
    rw [h s hs hz, sub_self, abs_zero]
    exact hα
  · intro h s hs hz
    by_contra hne
    have hpos : 0 < |s.re - 1 / 2| := abs_pos.2 (sub_ne_zero.2 hne)
    exact lt_irrefl _ (h _ hpos s hs hz)

/-- **Masullo's route**: the gap at every width, answered R136a1, gives GRH for the series `f` continues. -/
theorem grh_of_masullo {a : ℕ → ℂ} {f : ℂ → ℂ} (hf : Continues a f)
    (h : R136a1 "Masullo: the exterior zeros cancel at every width" (∀ α : ℝ, 0 < α → Gap f α)) : SeriesGRH a :=
  (grh_iff hf).2 ((onLine_iff_gap f).2 (R136a1.out h))

/-- **The open step is the claim**: the gap at every width is equivalent to GRH. The route's one open step carries the
whole conclusion. -/
theorem masullo_gap_iff_grh {a : ℕ → ℂ} {f : ℂ → ℂ} (hf : Continues a f) : (∀ α : ℝ, 0 < α → Gap f α) ↔ SeriesGRH a :=
  (onLine_iff_gap f).symm.trans (grh_iff hf).symm

/-- **Masullo's route over the Hecke family gives the Riemann hypothesis**: one continuation per member, each with
its gap answered R136a1. -/
theorem riemannHypothesis_of_masullo (H : HeckeFamily) (L : (ℕ → ℂ) → ℂ → ℂ) (hL : ∀ a ∈ H.coeffs, Continues a (L a))
    (h : ∀ a ∈ H.coeffs, R136a1 "Masullo: the exterior zeros cancel at every width" (∀ α : ℝ, 0 < α → Gap (L a) α)) :
    RiemannHypothesis :=
  riemannHypothesis_of_hecke fun a ha => grh_of_masullo (hL a ha) (h a ha)

end Arsenal.GRH
