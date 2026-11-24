/-
Birch and Swinnerton-Dyer, the algebraic side: the group of points and its rank.
Released under the Apache License 2.0.
-/

import Mathlib
import Arsenal.R136a1

/-!
# The algebraic side: `E(K)`, its torsion and its rank

Over any number field `K` (Mathlib's heights, Northcott's property and descent hold there, not only over `ℚ`):

* `Pts W`, the group `E(K)` (Mathlib's nonsingular points with the point at infinity, chord-tangent law);
* `mordellWeil_of_weak`: `E(K)` is finitely generated once `E(K)/2E(K)` is finite (`WeakMordellWeil`, answered R136a1:
  classical, not in Mathlib);
* `torsion_finite`: the torsion of `E(K)` is finite, unconditionally;
* `algRank`: the rank of `E(K)` as a `ℤ`-module, in `ℕ∞`, from `Module.rank`. It is the true rank whether or not
  `E(K)` is known to be finitely generated (no junk value), `⊤` exactly when there are infinitely many independent points;
* `algRank_eq_zero_iff`: rank zero is finiteness of `E(K)`, unconditionally (finite torsion is enough, Mordell-Weil is
  not needed).
-/

namespace Arsenal.BSD

open WeierstrassCurve

/-- The group `E(K)` of a Weierstrass curve over a field (Mathlib's nonsingular affine points with the point at infinity,
with the chord-tangent law). -/
abbrev Pts {K : Type*} [Field K] (W : WeierstrassCurve K) : Type _ := W.toAffine.Point

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- **Weak Mordell-Weil** (the named statement): `2 E(K)` has finite index in `E(K)`, i.e. `E(K)/2E(K)` is finite.
Classical (Mordell 1922, Weil 1929; the proof uses the finiteness of class groups and of unit groups modulo squares);
not in Mathlib. -/
def WeakMordellWeil (W : WeierstrassCurve K) : Prop :=
  (nsmulAddMonoidHom (α := Pts W) 2).range.FiniteIndex

/-- **The algebraic rank** of `E(K)`: its rank as a `ℤ`-module (the largest number of independent points), in `ℕ∞`.
Defined for every Weierstrass curve over every field, with no junk value. -/
noncomputable def algRank (W : WeierstrassCurve K) : ℕ∞ := Cardinal.toENat (Module.rank ℤ (Pts W))

/-- **Rank zero is all torsion**: `algRank W = 0` exactly when every point has finite order. -/
theorem algRank_eq_zero_iff_torsion (W : WeierstrassCurve K) :
    algRank W = 0 ↔ ∀ P : Pts W, IsOfFinAddOrder P := by
  unfold algRank
  rw [Cardinal.toENat_eq_zero, rank_eq_zero_iff]
  exact forall_congr' fun P => isOfFinAddOrder_iff_zsmul_eq_zero.symm

/-- **The rank is the `finrank`** once `E(K)` is finitely generated (so it is then finite). -/
theorem algRank_eq_finrank (W : WeierstrassCurve K) (hfg : AddGroup.FG (Pts W)) :
    algRank W = Module.finrank ℤ (Pts W) := by
  have : Module.Finite ℤ (Pts W) := Module.Finite.iff_addGroup_fg.2 hfg
  exact Cardinal.toENat_eq_natCast.2 (Module.finrank_eq_rank ℤ (Pts W)).symm

theorem algRank_ne_top (W : WeierstrassCurve K) (hfg : AddGroup.FG (Pts W)) : algRank W ≠ ⊤ := by
  rw [algRank_eq_finrank W hfg]; exact ENat.natCast_ne_top _

end Field

section NumberField

variable {K : Type*} [Field K] [DecidableEq K] [NumberField K]

/-- **Mordell-Weil from weak Mordell-Weil**: if `E(K)/2E(K)` is finite, `E(K)` is finitely generated. The proof is
Mathlib's descent theorem with the naive height: it is nonnegative, satisfies the approximate parallelogram law, and has
Northcott's property over number fields. -/
theorem mordellWeil_of_weak (W : WeierstrassCurve K) [W.IsElliptic]
    (h : R136a1 "weak Mordell-Weil" (WeakMordellWeil W)) : AddGroup.FG (Pts W) := by
  obtain ⟨C, hC⟩ := WeierstrassCurve.Affine.approx_parallelogram_law (W := W.toAffine)
  exact AddCommGroup.fg_of_descent' (h := WeierstrassCurve.Affine.Point.naiveHeight) h.out
    (fun P => by rw [WeierstrassCurve.Affine.Point.naiveHeight_eq_logHeight]; exact Height.logHeight_nonneg _) hC

/-- **The torsion of `E(K)` is finite**, unconditionally (Mathlib's `finite_torsion`, from the same height). -/
theorem torsion_finite (W : WeierstrassCurve K) [W.IsElliptic] : Finite (AddCommGroup.torsion (Pts W)) :=
  WeierstrassCurve.Affine.finite_torsion (W := W.toAffine)

/-- **Rank zero is finiteness**: `algRank W = 0` exactly when `E(K)` is finite (every point is then torsion, and the
torsion is finite). Unconditional: Mordell-Weil is not needed. -/
theorem algRank_eq_zero_iff (W : WeierstrassCurve K) [W.IsElliptic] : algRank W = 0 ↔ Finite (Pts W) := by
  rw [algRank_eq_zero_iff_torsion]
  constructor
  · intro hT
    have := torsion_finite W
    exact Finite.of_injective (fun x => (⟨x, hT x⟩ : AddCommGroup.torsion (Pts W)))
      (fun x y hxy => congrArg Subtype.val hxy)
  · intro _ P
    exact isOfFinAddOrder_of_finite P

/-- **Points of infinite order exist exactly when the rank is positive**, unconditionally. -/
theorem infinite_iff_algRank_pos (W : WeierstrassCurve K) [W.IsElliptic] : Infinite (Pts W) ↔ 0 < algRank W := by
  rw [pos_iff_ne_zero, Ne, algRank_eq_zero_iff W, not_finite_iff_infinite]

end NumberField

end Arsenal.BSD
