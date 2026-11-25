/-
Observable systems: every one has a one-box description, and a route to its proof.
Released under the Apache License 2.0.
-/
import Mathlib
import Arsenal.R136a1
import Arsenal.Rotation
import Arsenal.FullTurn

/-!
# Observable systems and their one-box description

**The statement.** Every observable system has a one-box description that is DMP-complete exactly when its claim holds; from
it follows a route to the proof, and once that route is shown, its truth is certified universally: at every tick, and, with
the gate shared across scales, at every scale.

**An observable system** (`Observable`) has states, one step (the tick) and, at each state, the system's own claim about what
is observed there (a decidable proposition). Its **one-box description** (`Observable.box`) is a box of the rotation API
(`Arsenal.Rotation.Box`) with the same states and step, whose marker is the system's claim (`inside`) and whose gate reads
the truth of the claim. The marker is never read off the gate, so the test has content (`Box.selfMarked_complete` is the case it
avoids).

**What is proved.**
* `box_complete_iff` (*representation*): for every observable system, the box is DMP-complete from a start exactly when the
  claim holds at every tick from it. By construction: the description restates the claim, it proves nothing by itself.
* `route` (*a route to the proof*): the claim at the start and a step that keeps the claim give DMP-completeness, so the claim
  at every tick (the one-box certificate). `route_iff` is the exact form along the run.
* `route_everywhere` (*certified universally*): with the gate shared across scales (answered `R136a1`: a named hypothesis,
  never an axiom), the route certifies every scale.
* `refuted_by_tick` (*falsifiable*): one tick where the claim fails refutes DMP-completeness.
* `ofReading` and `turn_gate` (*the gate by one turn*): when the observation is a real reading against a margin, the box is
  DMP-complete exactly when every reading is within the margin; when the reading is a coefficient hidden in a sum of `N`
  powers of a root of unity, one full turn computes it exactly, so the gate can be read by one turn (`Arsenal.FullTurn`).

Mathlib alone, nothing open.
-/

noncomputable section

namespace Arsenal

open Arsenal.Rotation

universe u

/-- **An observable system**: states, one step (the tick), and the system's own claim at each state. -/
structure Observable where
  /-- The states. -/
  X : Type u
  /-- The step: the tick. -/
  step : X → X
  /-- The system's own claim at each state. -/
  claim : X → Prop
  /-- The claim can be read at each state. -/
  dec : DecidablePred claim

namespace Observable

/-- **The one-box description**: the same states and step; the marker is the system's claim (`inside`), the gate reads the
truth of the claim (factor `0` when it holds, `1` when it fails, margin `0`). -/
def box (S : Observable.{u}) : Box.{u} :=
  haveI := S.dec
  ⟨S.X, S.step, fun x => if S.claim x then 0 else 1, 0, fun _ => .inside⟩

/-- The marker is correct exactly when the claim holds. -/
theorem correct_iff (S : Observable.{u}) (x : S.X) : S.box.Correct x ↔ S.claim x := by
  by_cases h : S.claim x
  · simp [box, Box.Correct, Box.gate, h]
  · simp [box, Box.Correct, Box.gate, h]

/-- **Representation**: the one-box description is DMP-complete from `x₀` exactly when the claim holds at every tick from `x₀`.
By construction, for every observable system. -/
theorem box_complete_iff (S : Observable.{u}) (x₀ : S.X) :
    S.box.DMPComplete x₀ ↔ ∀ n, S.claim (S.step^[n] x₀) := by
  constructor
  · intro h n; exact (S.correct_iff _).1 (h n)
  · intro h n; exact (S.correct_iff _).2 (h n)

/-- **A route to the proof**: the claim at the start and a step that keeps the claim make the one-box description DMP-complete,
so the claim holds at every tick. -/
theorem route (S : Observable.{u}) {x₀ : S.X} (h0 : S.claim x₀) (hstep : ∀ x, S.claim x → S.claim (S.step x)) :
    S.box.DMPComplete x₀ :=
  S.box.onebox_certificate ((S.correct_iff x₀).2 h0)
    (fun x hx => (S.correct_iff (S.step x)).2 (hstep x ((S.correct_iff x).1 hx)))

/-- **The route, exact along the run**: DMP-complete exactly when the claim holds at the start and every tick of the run passes
it on. -/
theorem route_iff (S : Observable.{u}) (x₀ : S.X) : S.box.DMPComplete x₀ ↔
    S.claim x₀ ∧ ∀ n, S.claim (S.step^[n] x₀) → S.claim (S.step^[n + 1] x₀) := by
  refine (Box.dmpComplete_iff_orbit S.box x₀).trans ?_
  constructor
  · rintro ⟨h0, hs⟩
    exact ⟨(S.correct_iff _).1 h0, fun n hn => (S.correct_iff _).1 (hs n ((S.correct_iff _).2 hn))⟩
  · rintro ⟨h0, hs⟩
    exact ⟨(S.correct_iff _).2 h0, fun n hn => (S.correct_iff _).2 (hs n ((S.correct_iff _).1 hn))⟩

/-- **Certified universally**: once the route is shown, the claim is certified at every tick, and, with the gate shared across
scales (a named hypothesis), at every tick of every scale. -/
theorem route_everywhere (S : Observable.{u}) {x₀ : S.X} (h0 : S.claim x₀)
    (hstep : ∀ x, S.claim x → S.claim (S.step x)) {ι : Type*} (C : ι → Box) (x : ∀ j, (C j).X)
    (hshared : R136a1 "the gate is shared across scales" (Box.SharedGate S.box x₀ C x)) :
    ∀ j, (C j).DMPComplete (x j) :=
  Box.scale_certificate S.box C x (S.route h0 hstep) hshared

/-- **Falsifiable**: one tick where the claim fails refutes DMP-completeness. -/
theorem refuted_by_tick (S : Observable.{u}) {x₀ : S.X} (n : ℕ) (hn : ¬ S.claim (S.step^[n] x₀)) :
    ¬ S.box.DMPComplete x₀ :=
  fun h => hn ((S.box_complete_iff x₀).1 h n)

/-! ## The observation as a reading, and the gate by one turn -/

/-- **An observable system read against a margin**: the claim at `x` is that the reading `read x` is within the margin `θ`. -/
def ofReading (X : Type u) (step : X → X) (read : X → ℝ) (θ : ℝ) : Observable.{u} :=
  ⟨X, step, fun x => read x ≤ θ, fun _ => inferInstance⟩

/-- The one-box description of a reading is DMP-complete exactly when every reading along the run is within the margin. -/
theorem ofReading_complete_iff (X : Type u) (step : X → X) (read : X → ℝ) (θ : ℝ) (x₀ : X) :
    (ofReading X step read θ).box.DMPComplete x₀ ↔ ∀ n, read (step^[n] x₀) ≤ θ :=
  (ofReading X step read θ).box_complete_iff x₀

/-- **The gate by one turn**: if the reading at each state is the real part of the `k`-th coefficient `c x k` of a sum of `N`
powers of a primitive `N`-th root of unity `ζ`, then one full turn computes it exactly, so reading the gate by the turn and
reading the coefficient give the same one-box description, DMP-complete under the same condition. -/
theorem turn_gate (X : Type u) (step : X → X) (θ : ℝ) {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (c : X → ℕ → ℂ)
    {k : ℕ} (hk : k < N) (x₀ : X) :
    (ofReading X step (fun x => ((N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
        (∑ m ∈ Finset.range N, c x m * ζ ^ (j * m)) * ζ ^ (j * (N - k))).re) θ).box.DMPComplete x₀ ↔
      ∀ n, (c (step^[n] x₀) k).re ≤ θ := by
  rw [ofReading_complete_iff]
  simp only [Arsenal.FullTurn.full_turn_coeff hζ _ hk]

end Observable

end Arsenal
