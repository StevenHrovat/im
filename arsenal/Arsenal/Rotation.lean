/-
The rotation API: one box, one command, one test.
Released under the Apache License 2.0.
-/
import Mathlib
import Arsenal.R136a1

/-!
# The rotation API

**The box.** A box has states, **one command** (`step`, the universal tick at the one shared gate), the **gate factor**
`fac` of the boundary the next step crosses, a **margin** `θ`, and the **marker** `mark x` it produces at each state:
`inside`, or `r136a1` (outside, `Arsenal.R136a1`). There is no outside input: the outside is read through the same gate by
the half-turn (`Gate`), whose reading is the same on both sides (`complete_halfTurn`).

**The test.** The gate's own verdict at `x` is `inside` when `fac x ≤ θ` and `r136a1` otherwise (`gate`). The marker is
**correct** at `x` when it agrees with that verdict (`Correct`), never with an outside oracle. `DMPComplete x`: every tick
from `x` gives the correct marker. One wrong marker, and the box is not DMP-complete.

**What is proved.**
* *The one-box certificate* (`onebox_certificate`, exact form `dmpComplete_iff_orbit`): correct at the start, and one step
  at the shared gate keeps it correct, so correct at every tick.
* *The scale certificate* (`scale_certificate`, `onebox_everywhere`): if every scale's box is rebuilt from the one box
  through its gate (`SharedGate`: same margin, a map keeping step and gate factor, start to start, carrying the marker), a
  box certified at one scale is correct at every scale. The sharing is answered `R136a1`: it is a named hypothesis of the
  theorem, never an axiom. A scale with a wrong marker refutes it (`not_shared_of_wrong`); it is satisfiable
  (`sharedGate_self`).
* *A finite check* (`complete_iff_bounded`): when the markers are correct from some tick on, DMP-completeness is the check
  of the ticks below it.
* *Vacuity checks*: a marker read off the gate afterwards always passes (`selfMarked_complete`), so the test has content
  only when the marker is the system's own claim; a box with a wrong marker exists (`exists_not_complete`).

The instances (a running system with its ledger, the universal machine, Yang-Mills, Navier-Stokes) are built on this
module where they are used.
-/

noncomputable section

namespace Arsenal.Rotation

universe u v w

/-- **The marker** a step produces: `inside`, or `r136a1` (outside). -/
inductive Marker
  | inside
  | r136a1
  deriving DecidableEq

/-- **The box**: states, one command (the step at the one shared gate), the gate factor, a margin, and the marker the box
produces at each state. -/
structure Box where
  /-- The states. -/
  X : Type u
  /-- The one command: the step at the shared gate (the universal tick). -/
  step : X → X
  /-- The gate factor of the boundary the next step crosses. -/
  fac : X → ℝ
  /-- The gate margin. -/
  θ : ℝ
  /-- The marker the box produces at each state. -/
  mark : X → Marker

namespace Box

/-- **The gate's own verdict**: `inside` when the gate factor is within the margin, `r136a1` otherwise. -/
def gate (B : Box.{u}) (x : B.X) : Marker := if B.fac x ≤ B.θ then .inside else .r136a1

/-- **The marker is correct** at `x`: it agrees with the gate's own verdict. -/
def Correct (B : Box.{u}) (x : B.X) : Prop := B.mark x = B.gate x

/-- **DMP-complete from `x`**: every tick from `x` gives the correct marker. -/
def DMPComplete (B : Box.{u}) (x : B.X) : Prop := ∀ n, B.Correct (B.step^[n] x)

/-- **The test settles from `x`**: from some tick on, every marker is correct. -/
def Settles (B : Box.{u}) (x : B.X) : Prop := ∃ N, ∀ n ≥ N, B.Correct (B.step^[n] x)

theorem gate_eq_inside_iff (B : Box.{u}) (x : B.X) : B.gate x = .inside ↔ B.fac x ≤ B.θ := by
  unfold gate
  split_ifs with h <;> simp [h]

theorem gate_eq_r136a1_iff (B : Box.{u}) (x : B.X) : B.gate x = .r136a1 ↔ B.θ < B.fac x := by
  unfold gate
  by_cases h : B.fac x ≤ B.θ
  · simp [h, not_lt.2 h]
  · simp [h, lt_of_not_ge h]

/-- DMP-completeness is carried along the run. -/
theorem DMPComplete.step {B : Box.{u}} {x : B.X} (h : B.DMPComplete x) : B.DMPComplete (B.step x) :=
  fun n => by
    have := h (n + 1)
    rwa [Function.iterate_succ_apply] at this

theorem DMPComplete.settles {B : Box.{u}} {x : B.X} (h : B.DMPComplete x) : B.Settles x := ⟨0, fun n _ => h n⟩

/-! ## The one-box certificate -/

/-- **The one-box certificate.** Correct at the start, and one step at the gate shared by every tick keeps it correct:
then the marker is correct at every tick. -/
theorem onebox_certificate (B : Box.{u}) {x₀ : B.X} (h0 : B.Correct x₀)
    (hstep : ∀ x, B.Correct x → B.Correct (B.step x)) : B.DMPComplete x₀ := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => rw [Function.iterate_succ_apply']; exact hstep _ ih

/-- **The certificate is exact along the run.** -/
theorem dmpComplete_iff_orbit (B : Box.{u}) (x₀ : B.X) : B.DMPComplete x₀ ↔
    B.Correct x₀ ∧ ∀ n, B.Correct (B.step^[n] x₀) → B.Correct (B.step^[n + 1] x₀) := by
  refine ⟨fun h => ⟨h 0, fun n _ => h (n + 1)⟩, fun ⟨h0, hs⟩ n => ?_⟩
  induction n with
  | zero => exact h0
  | succ n ih => exact hs n ih

/-- **A finite check**: if the markers are correct from tick `N` on, DMP-completeness is the check of the ticks below
`N`. -/
theorem complete_iff_bounded (B : Box.{u}) (x : B.X) {N : ℕ} (hN : ∀ n ≥ N, B.Correct (B.step^[n] x)) :
    B.DMPComplete x ↔ ∀ n < N, B.Correct (B.step^[n] x) :=
  ⟨fun h n _ => h n, fun h n => (lt_or_ge n N).elim (h n) (hN n)⟩

/-! ## The half-turn: the outside is read through the same gate -/

/-- **A two-sided gate**: the reading from inside, the reading after the half-turn, and the law that they agree. -/
structure Gate (X : Type*) (G : Type*) where
  /-- The reading from inside. -/
  inner : X → G
  /-- The reading after the half-turn (from the other side). -/
  outer : X → G
  /-- The law is the same on both sides. -/
  flux : ∀ x, outer x = inner x

/-- **The half-turn changes no verdict.** -/
theorem Gate.halfTurn {X G : Type*} (g : Gate X G) (v : G → Marker) (x : X) : v (g.outer x) = v (g.inner x) := by
  rw [g.flux]

/-- The test with the gate read through a reading `r` instead of the factor. -/
def CompleteVia (B : Box.{u}) (r : B.X → ℝ) (x : B.X) : Prop :=
  ∀ n, B.mark (B.step^[n] x) = if r (B.step^[n] x) ≤ B.θ then .inside else .r136a1

/-- **No outside input**: for a two-sided gate whose inside reading is the gate factor, the test read after the half-turn
is the test. -/
theorem complete_halfTurn (B : Box.{u}) (g : Gate B.X ℝ) (hin : ∀ x, g.inner x = B.fac x) (x : B.X) :
    B.CompleteVia g.outer x ↔ B.DMPComplete x := by
  unfold CompleteVia DMPComplete
  refine forall_congr' fun n => ?_
  rw [g.flux, hin]
  rfl

/-! ## The scale certificate -/

/-- **A reconstruction through the gate**: a map of states that keeps the step and the gate factor. -/
structure Hom (C : Box.{v}) (B : Box.{u}) where
  /-- The map of states. -/
  toFun : C.X → B.X
  step_comm : ∀ y, toFun (C.step y) = B.step (toFun y)
  fac_eq : ∀ y, B.fac (toFun y) = C.fac y

/-- The identity reconstruction. -/
def Hom.id (B : Box.{u}) : Hom B B := ⟨fun x => x, fun _ => rfl, fun _ => rfl⟩

theorem Hom.iterate_comm {C : Box.{v}} {B : Box.{u}} (φ : Hom C B) (n : ℕ) (y : C.X) :
    φ.toFun (C.step^[n] y) = B.step^[n] (φ.toFun y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, φ.step_comm]

/-- **The gate is shared across scales**: every scale's box has the same margin and is rebuilt from the one box through
its gate, start to start, carrying the marker. -/
def SharedGate (B : Box.{u}) (x₀ : B.X) {ι : Type w} (C : ι → Box.{v}) (x : ∀ j, (C j).X) : Prop :=
  ∀ j, (C j).θ = B.θ ∧ ∃ φ : Hom (C j) B, φ.toFun (x j) = x₀ ∧ ∀ y, B.mark (φ.toFun y) = (C j).mark y

/-- Along a reconstruction, correctness is read on the one box. -/
theorem correct_hom {B : Box.{u}} {C : Box.{v}} (φ : Hom C B) (hθ : C.θ = B.θ)
    (hmk : ∀ y, B.mark (φ.toFun y) = C.mark y) (y : C.X) : C.Correct y ↔ B.Correct (φ.toFun y) := by
  unfold Correct gate
  rw [hmk, φ.fac_eq, hθ]

/-- DMP-completeness pulls back along a reconstruction. -/
theorem dmpComplete_hom {B : Box.{u}} {C : Box.{v}} (φ : Hom C B) (hθ : C.θ = B.θ)
    (hmk : ∀ y, B.mark (φ.toFun y) = C.mark y) {y : C.X} (h : B.DMPComplete (φ.toFun y)) : C.DMPComplete y :=
  fun n => (correct_hom φ hθ hmk _).2 (by rw [φ.iterate_comm]; exact h n)

/-- **The scale certificate.** A box certified at one scale is correct at every scale, provided the gate is shared across
scales. The sharing is answered R136a1: named, carried as a hypothesis, never proved here. -/
theorem scale_certificate (B : Box.{u}) {x₀ : B.X} {ι : Type w} (C : ι → Box.{v}) (x : ∀ j, (C j).X)
    (hB : B.DMPComplete x₀)
    (hshared : R136a1 "the gate is shared across scales" (SharedGate B x₀ C x)) :
    ∀ j, (C j).DMPComplete (x j) := fun j => by
  obtain ⟨hθ, φ, hx, hmk⟩ := hshared.out j
  exact dmpComplete_hom φ hθ hmk (by rw [hx]; exact hB)

/-- **One box, every scale**: the one-box certificate and the shared gate give the correct marker at every tick of every
scale. -/
theorem onebox_everywhere (B : Box.{u}) {x₀ : B.X} (h0 : B.Correct x₀)
    (hstep : ∀ x, B.Correct x → B.Correct (B.step x)) {ι : Type w} (C : ι → Box.{v}) (x : ∀ j, (C j).X)
    (hshared : R136a1 "the gate is shared across scales" (SharedGate B x₀ C x)) :
    ∀ j, (C j).DMPComplete (x j) :=
  scale_certificate B C x (B.onebox_certificate h0 hstep) hshared

/-- **The sharing is falsifiable**: a certified one box and a scale with a wrong marker refute it. -/
theorem not_shared_of_wrong (B : Box.{u}) {x₀ : B.X} {ι : Type w} (C : ι → Box.{v}) (x : ∀ j, (C j).X)
    (hB : B.DMPComplete x₀) (j : ι) (hj : ¬ (C j).DMPComplete (x j)) : ¬ SharedGate B x₀ C x :=
  fun h => hj (scale_certificate B C x hB h j)

/-- The sharing is satisfiable: the one box shares its gate with itself. -/
theorem sharedGate_self (B : Box.{u}) (x₀ : B.X) (ι : Type w) :
    SharedGate B x₀ (fun _ : ι => B) (fun _ => x₀) :=
  fun _ => ⟨rfl, Hom.id B, rfl, fun _ => rfl⟩

/-! ## Vacuity checks -/

/-- **The self-marked box**: marked by its own gate verdict. -/
def selfMarked (X : Type u) (step : X → X) (fac : X → ℝ) (θ : ℝ) : Box.{u} :=
  ⟨X, step, fac, θ, fun x => if fac x ≤ θ then .inside else .r136a1⟩

/-- **A marker read off the gate afterwards always passes**: the test has content only when the marker is the system's
own claim. -/
theorem selfMarked_complete (X : Type u) (step : X → X) (fac : X → ℝ) (θ : ℝ) (x : X) :
    (selfMarked X step fac θ).DMPComplete x := fun _ => rfl

/-- **A wrong marker exists**: one state, factor `0`, margin `0` (the gate reads `inside`), marked `r136a1`. -/
theorem exists_not_complete : ∃ (B : Box.{u}) (x : B.X), ¬ B.DMPComplete x := by
  refine ⟨⟨PUnit, id, fun _ => 0, 0, fun _ => .r136a1⟩, PUnit.unit, fun h => ?_⟩
  have h0 : Marker.r136a1 = if (0 : ℝ) ≤ 0 then Marker.inside else Marker.r136a1 := h 0
  simp only [le_refl, ↓reduceIte] at h0
  exact Marker.noConfusion h0

end Box

end Arsenal.Rotation

end
