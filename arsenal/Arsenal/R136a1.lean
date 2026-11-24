/-
R136a1: the answer that places a part outside.
Released under the Apache License 2.0.
-/

/-!
# R136a1

In DMP (chapter 06, the flag; chapter 01, C∞) R136a1 is always a DMP-complete answer over IM, and a part answered R136a1 is
outside the system, whatever it is: nothing else needs to be proven about it.

In the arsenal this is the one way to leave a statement open. Where a proof would otherwise end in Lean's `sorry`, the statement
is named and taken as a hypothesis, `R136a1 "name" P`, by the theorems that use it. So:

* it never becomes an axiom: every declaration still rests on Lean's three standard axioms only, and the system stays one box
  (a `sorry` would make every declaration that uses it rest on `sorryAx`, tying the open part into everything built on it);
* it is distinguishable by its name, in the source and in every statement that carries it, and `tools/lint.sh` lists each one;
* the word `sorry` stays free for prose: the lint reads code only, never comments or strings.
-/

namespace Arsenal

/-- **R136a1**: the statement `P`, named `name`, answered as outside. It is `P` itself; a theorem that needs it takes it as a
hypothesis, so it is never assumed by the system, only by the theorem that names it. -/
def R136a1 (_name : String) (P : Prop) : Prop := P

/-- A part answered R136a1 is used exactly as the statement it names. -/
theorem R136a1.out {name : String} {P : Prop} (h : R136a1 name P) : P := h

end Arsenal
