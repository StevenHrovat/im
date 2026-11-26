/-
The translation layer: every problem as one card of the one-box API, with its single open step named.
Released under the Apache License 2.0.

The paper this layer serves: Draft 6 of GUID v8 (Gravity, `docs/paper/D6`,
https://github.com/StevenHrovat/gravity/blob/main/docs/paper/D6/latex/guid-v8-D6.pdf).
-/
import Mathlib
import Arsenal.R136a1
import Arsenal.Observable
import Arsenal.BSD
import Arsenal.RHLibrary

/-!
# The translation layer: all problems, one card shape, one gate

**What it is.** One DMP-native shape for every problem (`Card`): a name and a statement. Its translation into the rotation API
is one observable system with one state (`Card.observable`): one tick, the claim is the statement. Its one-box description is
DMP-complete exactly when the statement holds (`Card.complete_iff`). A list of cards (`Layer`) translates the same way into one
card, the conjunction (`Layer.card`), DMP-complete exactly when every card is (`Layer.complete_iff_each`).

**What it is not.** The translation is exact, in both directions, for every card. So it never decides a problem: it carries the
whole of each statement into the card's one open step, no more and no less. This is Draft 6's own finding ("No problem is
solved. The restatement holds exactly when the problem's statement holds at every step") and the arsenal's
(`Arsenal.GRH.masullo_gap_iff_grh`: the open step is the claim). A card is closed only by a proof of its statement, here or
outside; an outside proof enters answered R136a1, under its name (`Card.certified`).

**The seven Millennium Prize problems as one layer** (`millennium`):

| card | statement | how it is stated | status here |
|---|---|---|---|
| `riemann` | Mathlib's `RiemannHypothesis` | Mathlib | answered by the RH library (`Arsenal.RHLibrary.Input`) |
| `poincare` | every simply connected closed topological 3-manifold is homeomorphic to `S³` | Mathlib | answered by Perelman's proof (`PerelmanInput`) |
| `pVsNP` | P ≠ NP, for Mathlib's polynomial-time two-stack Turing machines on binary words | Mathlib | open |
| `bsd` | BSD (rank part) for every elliptic curve over `ℚ` (`Arsenal.BSD.BSDStatement`) | Mathlib | open |
| `navierStokes` | the statement is supplied | supplied | open |
| `yangMills` | the statement is supplied | supplied | open |
| `hodge` | the statement is supplied | supplied | open |

*Supplied* means Mathlib v4.34.0 cannot state it: no smooth solutions of PDE on `ℝ³ × [0, ∞)` with the decay conditions of
Fefferman's problem description (Navier-Stokes), no quantum Yang-Mills theory on `ℝ⁴` (Yang-Mills), no algebraic cycles and
Hodge classes of projective varieties (Hodge). The card takes the statement as a parameter, so whoever formalizes it supplies it
(as `Arsenal.GRH.HeckeFamily` is supplied). For Navier-Stokes a disproof of Fefferman's (A) and (B) is claimed
(Alpoge-Buckmaster, 2026-11-20, not refereed, its certificate not released; Gravity's `NavierStokesAPI`); the card does not
use it.

**What is proved** (Mathlib only, nothing open): the exact translation (`Card.complete_iff`, `Layer.complete_iff_each`), its
falsifiability (`Card.refuted`), the layer as the conjunction of the seven (`millennium_complete_iff`), and, with the two outside
inputs, exactly what is left (`millennium_left`): the layer is DMP-complete exactly when P ≠ NP, BSD over `ℚ` and the three supplied
statements hold. Standard axioms only.
-/

noncomputable section

namespace Arsenal.Problems

/-- **How a statement enters**: written in Mathlib, or supplied by whoever formalizes it. -/
inductive Stated
  | mathlib
  | supplied
  deriving DecidableEq

/-- **A card**: one problem in the layer's one shape, a name and its statement. -/
structure Card where
  /-- The problem's name. -/
  name : String
  /-- The statement the problem asks for. -/
  Statement : Prop
  /-- How the statement entered. -/
  stated : Stated

namespace Card

/-- **The translation**: a card as an observable system with one state; the tick stays, the claim is the statement. -/
abbrev observable (c : Card) : Observable.{0} :=
  ⟨Unit, id, fun _ => c.Statement, Classical.decPred _⟩

/-- **The translation is exact**: the card's one-box description is DMP-complete exactly when its statement holds. -/
theorem complete_iff (c : Card) : c.observable.box.DMPComplete () ↔ c.Statement :=
  (c.observable.box_complete_iff ()).trans ⟨fun h => h 0, fun h _ => h⟩

/-- **Falsifiable**: a refutation of the statement refutes the card. -/
theorem refuted (c : Card) (h : ¬ c.Statement) : ¬ c.observable.box.DMPComplete () :=
  fun hc => h (c.complete_iff.1 hc)

/-- **An outside proof certifies the card**: the statement, answered R136a1 under the proof's name. -/
theorem certified (c : Card) {name : String} (h : R136a1 name c.Statement) : c.observable.box.DMPComplete () :=
  c.complete_iff.2 (R136a1.out h)

end Card

/-- **A layer**: a list of cards. -/
abbrev Layer := List Card

/-- **The layer as one card**: its statement is that every card's statement holds. -/
def Layer.card (L : Layer) : Card :=
  ⟨"the layer", ∀ c ∈ L, c.Statement, .mathlib⟩

/-- **One gate for all**: the layer's box is DMP-complete exactly when every card's box is. -/
theorem Layer.complete_iff_each (L : Layer) :
    L.card.observable.box.DMPComplete () ↔ ∀ c ∈ L, c.observable.box.DMPComplete () := by
  rw [Card.complete_iff]
  exact forall₂_congr fun c _ => c.complete_iff.symm

/-! ## The statements Mathlib can write -/

/-- **The Riemann hypothesis**, Mathlib's statement. -/
def riemann : Card := ⟨"Riemann hypothesis", RiemannHypothesis, .mathlib⟩

/-- **The RH library answers it** (`Arsenal.RHLibrary`: its theorem 4 gives theorem 1 by the arsenal's ladder). -/
theorem riemann_of_library (h : RHLibrary.Input) : riemann.Statement :=
  RHLibrary.riemannHypothesis_of_zerosOnLine (RHLibrary.input_iff.1 h)

/-- **The Poincaré conjecture**, topological form: every simply connected, compact, Hausdorff topological manifold locally
modelled on `ℝ³` (closed: compact, without boundary) is homeomorphic to the unit sphere of `ℝ⁴`. Stated for manifolds in
`Type`. -/
def PoincareStatement : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [SimplyConnectedSpace M],
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

/-- The Poincaré conjecture as a card. -/
def poincare : Card := ⟨"Poincaré conjecture", PoincareStatement, .mathlib⟩

/-- **Perelman's proof, answered R136a1**: proved (Ricci flow with surgery, 2002-2003; accepted, the Clay prize awarded in
2010), not formalized in Lean, so outside. -/
abbrev PerelmanInput : Prop :=
  R136a1 "Perelman 2002-2003: the Poincare conjecture (Ricci flow with surgery), not formalized" PoincareStatement

/-- Binary words, the inputs of a decision problem. -/
abbrev Word := List Bool

/-- **A pair of words as one tape**: the first, a separator (`none`), the second. -/
def pairEnc (p : Word × Word) : List (Option Bool) := p.1.map some ++ none :: p.2.map some

/-- **P**: decided by a two-stack Turing machine in time polynomial in the input's length (Mathlib's
`Turing.TM2ComputableInPolyTime`). -/
def InP (L : Word → Prop) : Prop :=
  ∃ f : Word → Bool,
    Nonempty (Turing.TM2ComputableInPolyTime (fun w : Word => w) (fun b : Bool => [b]) f) ∧ ∀ w, L w ↔ f w = true

/-- **NP**: a polynomial-time verifier and certificates of polynomial length. -/
def InNP (L : Word → Prop) : Prop :=
  ∃ (V : Word × Word → Bool) (p : Polynomial ℕ),
    Nonempty (Turing.TM2ComputableInPolyTime pairEnc (fun b : Bool => [b]) V) ∧
      ∀ w, L w ↔ ∃ c : Word, c.length ≤ p.eval w.length ∧ V (w, c) = true

/-- **P ≠ NP**: some language in NP is not in P. -/
def PneNP : Prop := ∃ L : Word → Prop, InNP L ∧ ¬ InP L

/-- P versus NP as a card, in the direction most expect (P ≠ NP). A proof of P = NP refutes the card (`Card.refuted`) and
settles the problem the other way. -/
def pVsNP : Card := ⟨"P versus NP", PneNP, .mathlib⟩

/-- **Birch and Swinnerton-Dyer** (rank part) for every elliptic curve over `ℚ`, the Clay form, through
`Arsenal.BSD.BSDStatement` (which states it over every number field). -/
def bsd : Card :=
  ⟨"Birch and Swinnerton-Dyer", ∀ W : WeierstrassCurve ℚ, W.IsElliptic → Arsenal.BSD.BSDStatement W, .mathlib⟩

/-! ## The statements Mathlib cannot write yet: supplied -/

/-- Navier-Stokes, the statement supplied (one of Fefferman's (A) to (D)). -/
def navierStokes (S : Prop) : Card := ⟨"Navier-Stokes existence and smoothness", S, .supplied⟩

/-- Yang-Mills existence and mass gap, the statement supplied. -/
def yangMills (S : Prop) : Card := ⟨"Yang-Mills existence and mass gap", S, .supplied⟩

/-- The Hodge conjecture, the statement supplied. -/
def hodge (S : Prop) : Card := ⟨"Hodge conjecture", S, .supplied⟩

/-! ## The seven as one layer -/

/-- **The seven Millennium Prize problems as one layer.** -/
def millennium (ns ym hg : Prop) : Layer :=
  [riemann, poincare, pVsNP, bsd, navierStokes ns, yangMills ym, hodge hg]

/-- **The layer is the conjunction of the seven.** -/
theorem millennium_complete_iff (ns ym hg : Prop) :
    (millennium ns ym hg).card.observable.box.DMPComplete () ↔
      riemann.Statement ∧ poincare.Statement ∧ pVsNP.Statement ∧ bsd.Statement ∧ ns ∧ ym ∧ hg := by
  rw [Card.complete_iff]
  simp only [Layer.card, millennium, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  rfl

/-- **What is left**: with the RH library and Perelman's proof as the two outside inputs, the layer is DMP-complete exactly
when P ≠ NP, BSD over `ℚ` and the three supplied statements hold. These five are the layer's open steps. -/
theorem millennium_left (ns ym hg : Prop) (hRH : RHLibrary.Input) (hP : PerelmanInput) :
    (millennium ns ym hg).card.observable.box.DMPComplete () ↔ pVsNP.Statement ∧ bsd.Statement ∧ ns ∧ ym ∧ hg := by
  rw [millennium_complete_iff]
  exact ⟨fun h => h.2.2, fun h => ⟨riemann_of_library hRH, R136a1.out hP, h⟩⟩

end Arsenal.Problems
