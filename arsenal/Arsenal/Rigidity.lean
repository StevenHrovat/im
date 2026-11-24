/-
Rigidity as a one-box test.
Released under the Apache License 2.0.
-/
import Mathlib
import Arsenal.Rotation

/-!
# Rigidity as a one-box test

A manifold has finitely many *presentations* (its structure set), the manifold itself among them, and its self-equivalences act
on them. It is **rigid** when every presentation is the manifold itself seen through a self-equivalence (the criterion of
Kreck-Lueck for simply connected manifolds; here it is the definition, and the identification with a given manifold is the
user's named input).

**The rigidity box** (`RigidityData.box`). One tick per presentation, cycled. The gate reads `inside` when the presentation is
reached from the manifold by a self-equivalence, `r136a1` otherwise; the marker is the system's own claim, `inside` ("rigid").
The marker is never read off the gate, so the test has content (`Box.selfMarked_complete` is the case it avoids).

**What is proved.**
* `box_complete_iff`: the box is DMP-complete exactly when the manifold is rigid. Both directions, so the box carries exactly
  the rigidity question.
* `rigid_of_shared`: if the box shares the gate with a certified box (the sharing answered `R136a1`), the manifold is rigid.
  This is the corollary made into the next layer's named hypothesis: never an axiom.
* `not_shared_of_not_rigid`: a manifold that is not rigid refutes the sharing; the hypothesis is falsifiable.
* `twoPoint`: two presentations and a homomorphism `η` of the self-equivalences to `ZMod 2` acting by translation (the shape
  of a normal invariant in `Z/2`); `twoPoint_rigid_iff`: rigid exactly when `η` is onto.
* `exists_not_rigid`: a datum that is not rigid exists, so the box is not complete for every datum.
-/

noncomputable section

open Classical

namespace Arsenal.Rotation

universe u v w

/-- **A rigidity datum**: the presentations (finitely many), the manifold itself among them, and the self-equivalences acting
on them. -/
structure RigidityData where
  /-- The presentations (the structure set). -/
  P : Type u
  /-- There are finitely many. -/
  fin : Fintype P
  /-- The manifold itself. -/
  base : P
  /-- The self-equivalences. -/
  E : Type v
  /-- Their action on the presentations. -/
  act : E → P → P

namespace RigidityData

variable (R : RigidityData.{u, v})

instance : Fintype R.P := R.fin

/-- **Rigid**: every presentation is the manifold itself seen through a self-equivalence. -/
def Rigid : Prop := ∀ p : R.P, ∃ g : R.E, R.act g R.base = p

/-- The presentations in a fixed order, cycled. -/
def enum (n : ℕ) : R.P :=
  (Fintype.equivFin R.P).symm ⟨n % Fintype.card R.P, Nat.mod_lt _ (Fintype.card_pos_iff.2 ⟨R.base⟩)⟩

theorem enum_surjective : Function.Surjective R.enum := by
  intro p
  refine ⟨(Fintype.equivFin R.P p : ℕ), ?_⟩
  unfold enum
  have h : ((Fintype.equivFin R.P p : ℕ) % Fintype.card R.P) = (Fintype.equivFin R.P p : ℕ) :=
    Nat.mod_eq_of_lt (Fintype.equivFin R.P p).isLt
  simp only [h, Fin.eta, Equiv.symm_apply_apply]

/-- **The rigidity box**: one tick per presentation; the gate reads `inside` when the presentation is reached from the
manifold by a self-equivalence; the marker is the claim "rigid" (`inside`). -/
def box : Box.{0} where
  X := ℕ
  step := Nat.succ
  fac := fun n => if ∃ g : R.E, R.act g R.base = R.enum n then 0 else 1
  θ := 1 / 2
  mark := fun _ => .inside

theorem box_correct_iff (n : ℕ) : R.box.Correct n ↔ ∃ g : R.E, R.act g R.base = R.enum n := by
  unfold Box.Correct Box.gate
  by_cases h : ∃ g : R.E, R.act g R.base = R.enum n
  · have h0 : R.box.fac n ≤ R.box.θ := by
      show (if ∃ g : R.E, R.act g R.base = R.enum n then (0 : ℝ) else 1) ≤ 1 / 2
      rw [if_pos h]; norm_num
    rw [if_pos h0]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · have h1 : ¬ R.box.fac n ≤ R.box.θ := by
      show ¬ (if ∃ g : R.E, R.act g R.base = R.enum n then (0 : ℝ) else 1) ≤ 1 / 2
      rw [if_neg h]; norm_num
    rw [if_neg h1]
    exact ⟨fun e => absurd e (fun e' => Marker.noConfusion e'), fun e => absurd e h⟩

theorem box_iterate (n : ℕ) : R.box.step^[n] (0 : ℕ) = n := by
  show Nat.succ^[n] 0 = n
  rw [Nat.succ_iterate, zero_add]

/-- **The box carries exactly the rigidity question**: DMP-complete from the start exactly when the manifold is rigid. -/
theorem box_complete_iff : R.box.DMPComplete (0 : ℕ) ↔ R.Rigid := by
  unfold Box.DMPComplete
  constructor
  · intro h p
    obtain ⟨n, rfl⟩ := R.enum_surjective p
    have := h n
    rw [R.box_iterate] at this
    exact (R.box_correct_iff n).1 this
  · intro h n
    rw [R.box_iterate]
    exact (R.box_correct_iff n).2 (h _)

/-- **Rigid from the shared gate.** If the rigidity box shares the gate with a certified box, the manifold is rigid. The
sharing is answered R136a1: the corollary becomes the next layer's named hypothesis, never an axiom. -/
theorem rigid_of_shared (B : Box.{w}) {x₀ : B.X} (hB : B.DMPComplete x₀)
    (hshared : R136a1 "the gate is shared across scales"
      (Box.SharedGate B x₀ (fun _ : Unit => R.box) (fun _ => (0 : ℕ)))) : R.Rigid :=
  R.box_complete_iff.1 (Box.scale_certificate B (fun _ : Unit => R.box) (fun _ => (0 : ℕ)) hB hshared ())

/-- **Falsifiable**: a manifold that is not rigid refutes the sharing. -/
theorem not_shared_of_not_rigid (B : Box.{w}) {x₀ : B.X} (hB : B.DMPComplete x₀) (h : ¬ R.Rigid) :
    ¬ Box.SharedGate B x₀ (fun _ : Unit => R.box) (fun _ => (0 : ℕ)) :=
  fun hs => h (R.rigid_of_shared B hB hs)

end RigidityData

/-- **Two presentations**: the manifold (`0`) and one other (`1`), with the self-equivalences acting through a map `η` to
`ZMod 2` by translation: the shape of a normal invariant in `Z/2`. -/
def twoPoint (E : Type v) (η : E → ZMod 2) : RigidityData.{0, v} :=
  ⟨ZMod 2, inferInstance, 0, E, fun g p => η g + p⟩

/-- **Two presentations: rigid exactly when the normal invariant is onto.** -/
theorem twoPoint_rigid_iff (E : Type v) (η : E → ZMod 2) :
    (twoPoint E η).Rigid ↔ Function.Surjective η := by
  constructor
  · intro h p
    obtain ⟨g, hg⟩ := h p
    exact ⟨g, by simpa [twoPoint] using hg⟩
  · intro h p
    obtain ⟨g, hg⟩ := h p
    exact ⟨g, by simpa [twoPoint] using hg⟩

/-- **The test has content**: a datum that is not rigid exists (two presentations, one self-equivalence acting trivially). -/
theorem exists_not_rigid : ∃ R : RigidityData.{0, 0}, ¬ R.Rigid := by
  refine ⟨twoPoint Unit (fun _ => 0), fun h => ?_⟩
  obtain ⟨_, hg⟩ := (twoPoint_rigid_iff Unit (fun _ => (0 : ZMod 2))).1 h 1
  exact (show (0 : ZMod 2) ≠ 1 by decide) hg

end Arsenal.Rotation

end
