/-
Birch and Swinnerton-Dyer, the local data: point counts over finite rings that run.
Released under the Apache License 2.0.
-/

import Mathlib
import Arsenal.BSD.Algebraic

/-!
# Point counts that run

Computable over any finite commutative ring with decidable equality, read off the curve's own coefficients:

* `count W`: the affine solutions of the Weierstrass equation, plus the point at infinity;
* `frobTrace W = q + 1 - count W` (`q` the number of elements) and the decidable Hasse check `hasseCheck W`, which is the
  real inequality `|a| ≤ 2 √q` (`hasseCheck_iff`);
* `count_correct`: over a finite field, for an elliptic curve, `count` is Mathlib's `Nat.card` of `E(F)`;
* `reduceMod W p`: an integral curve read mod `p` (`count_reduceMod` at a prime of good reduction).

None of these is `noncomputable`; the examples at the end are checked by the kernel with `decide`.
-/

namespace Arsenal.BSD

section Ring

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

/-- **The number of points**, computed: the affine solutions of the Weierstrass equation over the finite ring `R`, plus
the point at infinity. -/
def count (W : WeierstrassCurve R) : ℕ :=
  (Finset.univ.filter fun xy : R × R =>
    xy.2 ^ 2 + W.a₁ * xy.1 * xy.2 + W.a₃ * xy.2 = xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆).card + 1

/-- **The trace of Frobenius** `a = q + 1 - #E`, computed (`q` the number of elements of `R`). -/
def frobTrace (W : WeierstrassCurve R) : ℤ := (Fintype.card R : ℤ) + 1 - count W

/-- **The Hasse check**, decidable: `a^2 ≤ 4 q`. -/
def hasseCheck (W : WeierstrassCurve R) : Bool := decide (frobTrace W ^ 2 ≤ 4 * (Fintype.card R : ℤ))

/-- **The check is the real Hasse inequality** `|a| ≤ 2 √q`. -/
theorem hasseCheck_iff (W : WeierstrassCurve R) :
    hasseCheck W = true ↔ |(frobTrace W : ℝ)| ≤ 2 * Real.sqrt (Fintype.card R) := by
  unfold hasseCheck
  rw [decide_eq_true_iff]
  set a := frobTrace W
  set q := Fintype.card R
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h2 : (2 * Real.sqrt q) ^ 2 = 4 * q := by rw [mul_pow, Real.sq_sqrt hq]; norm_num
  have habs : |2 * Real.sqrt q| = 2 * Real.sqrt q := abs_of_nonneg (by positivity)
  have hcast : (a ^ 2 ≤ 4 * (q : ℤ)) ↔ ((a : ℝ)) ^ 2 ≤ 4 * (q : ℝ) := by
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  rw [hcast, ← h2, sq_le_sq, habs]

end Ring

/-- **The computed count is Mathlib's.** Over a finite field, the number of points of an elliptic curve (Mathlib's
`Nat.card` of its group) is `count`. -/
theorem count_correct {F : Type*} [Field F] [Fintype F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic] :
    Nat.card (Pts W) = count W := by
  rw [Nat.card_congr (WeierstrassCurve.Affine.pointEquiv W.toAffine)]
  have hS : {xy : F × F // W.toAffine.Equation xy.1 xy.2} ≃
      {xy : F × F // xy.2 ^ 2 + W.a₁ * xy.1 * xy.2 + W.a₃ * xy.2 =
        xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆} :=
    Equiv.subtypeEquivRight fun xy => by rw [WeierstrassCurve.Affine.equation_iff]
  change Nat.card (Option {xy : F × F // W.toAffine.Equation xy.1 xy.2}) = _
  rw [Finite.card_option, Nat.card_congr hS, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-- An integral Weierstrass curve read mod `p`. -/
def reduceMod (W : WeierstrassCurve ℤ) (p : ℕ) : WeierstrassCurve (ZMod p) := W.map (Int.castRingHom (ZMod p))

/-- **The count mod `p` is Mathlib's** at every prime of good reduction (`Δ ≠ 0` mod `p`). -/
theorem count_reduceMod (W : WeierstrassCurve ℤ) (p : ℕ) [hp : Fact p.Prime] (hΔ : ((W.Δ : ℤ) : ZMod p) ≠ 0) :
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    Nat.card (Pts (reduceMod W p)) = count (reduceMod W p) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : (reduceMod W p).IsElliptic := ⟨by rw [reduceMod, WeierstrassCurve.map_Δ]; exact isUnit_iff_ne_zero.2 hΔ⟩
  exact count_correct (reduceMod W p)

/-- The count is the curve's own: `y² = x³ - x` mod `5` has `a_5 = -2`, checked by the kernel. -/
example : frobTrace (reduceMod ⟨0, 0, 0, -1, 0⟩ 5) = -2 := by decide

example : hasseCheck (reduceMod ⟨0, 0, 0, -1, 0⟩ 5) = true := by decide

end Arsenal.BSD
