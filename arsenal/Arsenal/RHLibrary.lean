/-
The Riemann hypothesis library merged into the arsenal: its five theorems as one input, in native IM form.
Released under the Apache License 2.0.

The library is `leanprover-community/riemann-hypothesis` (the proof is Levent Alpoge's; Apache License 2.0). It is not imported:
the arsenal requires Mathlib and its own core only. Its five statements enter word for word from its Mathlib-only statement file,
as one input answered R136a1. Everything else here is proved from Mathlib and `Arsenal.GRH`.
-/
import Mathlib
import Arsenal.R136a1
import Arsenal.GRH
import Arsenal.Observable

/-!
# The Riemann hypothesis library, merged

**The source.** The community mirror of the Lean proof of the Riemann hypothesis, read at commit
`de330e73d828ea08f621cb28395d48480806d00f` (branch `main`, 2026-11-26). Its file `src/Statements.lean` imports only Mathlib and
defines four statements; `src/Main.lean` proves five theorems about them (`riemannHypothesis`, `riemannZeta_eq_zero_re`,
`LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`), and `Challenge.lean` restates
them for the Comparator tool. The four definitions below are that file's text, character for character.

**Why R136a1 and not an import.** The library has about 175,000 modules on Lean v4.37.0-rc1 with a later Mathlib; the arsenal is on
Lean v4.34.0 and Mathlib v4.34.0 and requires nothing else (`tools/lint.sh`). So the five theorems are outside the arsenal: they
enter as one input, `Input`, answered R136a1 (a named hypothesis, never an axiom). The statements are the same text, elaborated
against Mathlib v4.34.0; the library's own check (the Comparator tool and several kernels) is against its Mathlib. A theorem
here that takes `Input` says exactly: *if* the five statements hold in Mathlib v4.34.0, then this follows.

**What the merge proves** (Mathlib and `Arsenal.GRH` only, nothing open):
* *the statements in the arsenal's words*: `riemannZetaZerosOnLine_iff` (the library's zeta statement is Mathlib's
  `RiemannHypothesis`), `dirichletLZerosOnLine_iff` (its GRH is `DirichletGRH` at every modulus);
* *one statement carries all five*: `library_iff`, the input is equivalent to `DirichletLZerosOnLine` (the library's theorem 4)
  alone. Theorem 1 follows by the arsenal's own ladder (`riemannHypothesis_of_dirichlet`, modulus `1`), theorem 2 is theorem 1,
  theorem 3 adds Mathlib's nonvanishing on `re s ≥ 1`, theorem 5 is a special case. So the library's two routes to the Riemann
  hypothesis (its own and the arsenal's ladder) are checked against each other here;
* *what the input answers*: GRH for every Dirichlet L-series and for zeta in the arsenal's coefficient form (`seriesGRH_of_input`,
  `zeta_seriesGRH_of_input`), and the gap of Masullo's route at every width for every Dirichlet L-function
  (`masullo_gap_of_input`). The Hecke and Dedekind cases (`HeckeGRH`, `DedekindGRH`) are not answered: the library proves
  Dirichlet L-functions only;
* *the one-box description*: the moduli as an observable system (one tick, the next modulus; the claim, GRH at that modulus)
  is DMP-complete exactly when GRH holds at every modulus (`moduli_complete_iff_input`), and the input certifies it
  (`moduli_certified`).

Standard axioms only.
-/

noncomputable section

namespace Arsenal.RHLibrary

open Arsenal.GRH

/-! ## The library's statements, word for word (`src/Statements.lean`) -/

/-- Every zero of `ζ` other than the trivial zeros and the point `1` has real part `1/2` (the library's statement). -/
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

/-- GRH, half-plane form: no Dirichlet L-function vanishes on `re s > 1/2`, the pole of the trivial character excepted (the
library's statement). -/
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- GRH for every Dirichlet character: the zeros in the strip lie on the line (the library's statement). -/
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- GRH for primitive Dirichlet characters (the library's statement). -/
def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- **The library**: its five theorems (`src/Main.lean`), field by field, under their names there. -/
structure Library : Prop where
  riemannHypothesis : RiemannHypothesis
  riemannZeta_eq_zero_re : RiemannZetaZerosOnLine
  LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf
  LFunction_eq_zero_re : DirichletLZerosOnLine
  LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine

/-- **The input**: the library, answered R136a1. It is outside the arsenal (not imported, not checked here), so every theorem
that uses it names it as a hypothesis. -/
abbrev Input : Prop :=
  R136a1 "leanprover-community/riemann-hypothesis at de330e7: the five theorems of src/Main.lean" Library

/-! ## The statements in the arsenal's words -/

/-- **The library's zeta statement is Mathlib's `RiemannHypothesis`**, by definition (the library proves its theorem 2 as
theorem 1). -/
theorem riemannZetaZerosOnLine_iff : RiemannZetaZerosOnLine ↔ RiemannHypothesis := Iff.rfl

/-- **The library's GRH is `DirichletGRH` at every modulus.** -/
theorem dirichletLZerosOnLine_iff : DirichletLZerosOnLine ↔ ∀ (N : ℕ) [NeZero N], DirichletGRH N := by
  constructor
  · intro h N _ χ s hs hz
    exact h N χ s hs.1 hs.2 hz
  · intro h N _ χ s h0 h1 hz
    exact h N χ s ⟨h0, h1⟩ hz

/-! ## One statement carries all five -/

/-- **Theorem 4 gives theorem 1 by the arsenal's ladder**: GRH at modulus `1` is the Riemann hypothesis. -/
theorem riemannHypothesis_of_zerosOnLine (h : DirichletLZerosOnLine) : RiemannHypothesis :=
  riemannHypothesis_of_dirichlet (dirichletLZerosOnLine_iff.1 h 1)

/-- **Theorem 4 gives theorem 3**: in the strip a zero right of `1/2` would be off the line; on `re s ≥ 1` Mathlib's
nonvanishing applies. -/
theorem nonvanishing_of_zerosOnLine (h : DirichletLZerosOnLine) : DirichletLNonvanishingRightOfHalf := by
  intro N _ χ s hs hχ hz
  rcases lt_or_ge s.re 1 with h1 | h1
  · have := h N χ s (by linarith) h1 hz
    linarith
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (s := s) hχ h1 hz

/-- **Theorem 4 gives theorem 5**, the primitive characters being among all. -/
theorem primitive_of_zerosOnLine (h : DirichletLZerosOnLine) : PrimitiveDirichletLZerosOnLine := by
  intro N _ χ _ s h0 h1 hz
  exact h N χ s h0 h1 hz

/-- **Theorem 4 alone gives the library.** -/
theorem library_of_zerosOnLine (h : DirichletLZerosOnLine) : Library where
  riemannHypothesis := riemannHypothesis_of_zerosOnLine h
  riemannZeta_eq_zero_re := riemannZetaZerosOnLine_iff.2 (riemannHypothesis_of_zerosOnLine h)
  LFunction_ne_zero_of_half_lt_re := nonvanishing_of_zerosOnLine h
  LFunction_eq_zero_re := h
  LFunction_eq_zero_re_of_isPrimitive := primitive_of_zerosOnLine h

/-- **The five are one statement**: the library holds exactly when its theorem 4 does. -/
theorem library_iff : Library ↔ DirichletLZerosOnLine :=
  ⟨fun L => L.LFunction_eq_zero_re, library_of_zerosOnLine⟩

/-- **The input, decoded**: exactly theorem 4 (`R136a1.iff`, then `library_iff`). -/
theorem input_iff : Input ↔ DirichletLZerosOnLine :=
  R136a1.iff.trans library_iff

/-! ## What the input answers -/

/-- **GRH at every modulus**, from the input. -/
theorem dirichletGRH_of_input (h : Input) (N : ℕ) [NeZero N] : DirichletGRH N :=
  dirichletLZerosOnLine_iff.1 (input_iff.1 h) N

/-- **GRH for every Dirichlet L-series**, in the arsenal's coefficient form. -/
theorem seriesGRH_of_input (h : Input) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) :
    SeriesGRH (fun n => χ n) :=
  (dirichletGRH_iff N).1 (dirichletGRH_of_input h N) χ

/-- **GRH for the series of `1`**: the zeta function, through modulus `1`. -/
theorem zeta_seriesGRH_of_input (h : Input) : SeriesGRH 1 :=
  (grh_iff continues_zeta).2 (onLine_zeta_of_dirichlet (dirichletGRH_of_input h 1))

/-- **Masullo's open step, answered for Dirichlet L-functions**: the gap at every width, from the input. The Hecke family
beyond the Dirichlet characters stays open. -/
theorem masullo_gap_of_input (h : Input) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∀ α : ℝ, 0 < α → Gap (DirichletCharacter.LFunction χ) α :=
  (onLine_iff_gap _).1 (dirichletGRH_of_input h N χ)

/-! ## The one-box description: the moduli as an observable system -/

/-- **The moduli as an observable system**: the state `n` stands for the modulus `n + 1`, one tick is the next modulus, and the
claim at `n` is GRH for every Dirichlet character of that modulus. -/
abbrev moduli : Observable.{0} where
  X := ℕ
  step := fun n => n + 1
  claim := fun n => DirichletGRH (n + 1)
  dec := Classical.decPred _

/-- The run from `0` visits every state: tick `n` is the state `n`. -/
theorem moduli_iterate (n : ℕ) : moduli.step^[n] (0 : ℕ) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]

/-- **Representation**: the one-box description of the moduli is DMP-complete exactly when GRH holds at every modulus. -/
theorem moduli_complete_iff : moduli.box.DMPComplete (0 : ℕ) ↔ ∀ n : ℕ, DirichletGRH (n + 1) :=
  (moduli.box_complete_iff (0 : ℕ)).trans (forall_congr' fun n => by rw [moduli_iterate])

/-- **The input certifies the box**: one route (the claim at modulus `1`, and the next modulus kept), so DMP-complete. -/
theorem moduli_certified (h : Input) : moduli.box.DMPComplete (0 : ℕ) :=
  moduli.route (dirichletGRH_of_input h (0 + 1)) (fun x _ => dirichletGRH_of_input h (x + 1 + 1))

/-- **The box and the input are the same statement**: DMP-complete exactly when the library's theorem 4 holds. -/
theorem moduli_complete_iff_input : moduli.box.DMPComplete (0 : ℕ) ↔ Input := by
  rw [moduli_complete_iff, input_iff, dirichletLZerosOnLine_iff]
  constructor
  · intro h N _
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
    exact h n
  · intro h n
    exact h (n + 1)

end Arsenal.RHLibrary
