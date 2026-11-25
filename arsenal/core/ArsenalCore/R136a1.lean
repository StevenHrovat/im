/-
R136a1: the answer that places a part outside, and the token every API input and output carries. On Lean's kernel alone.
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

**A token.** It lives in the core, which needs no library, so every API input and output carries the same token, whether the
statement is decided on the kernel alone or with Mathlib. A proven statement is issued as its token too (`R136a1.of`); then the
name travels with it. The first author reads a token as the quantization of the containing axiom system, proven through the one box.

**A valid encoding.** The token is the statement itself, so encoding a statement as its token and decoding it back is the identity
(`R136a1.iff`), and a token of a token is the token (`R136a1.idem`): the trivial encoding, which never loses anything. The first
author reads this as DMP.DMP (2 + 2 in mathematics, +-1 in existence) being a valid encoding, and so as the token's use as an encoder.
-/

namespace Arsenal

/-- **R136a1**: the statement `P`, named `name`, answered as outside. It is `P` itself; a theorem that needs it takes it as a
hypothesis, so it is never assumed by the system, only by the theorem that names it. -/
def R136a1 (_name : String) (P : Prop) : Prop := P

/-- A part answered R136a1 is used exactly as the statement it names. -/
theorem R136a1.out {name : String} {P : Prop} (h : R136a1 name P) : P := h

/-- **Issuing a token**: a proven statement is issued under its name. -/
theorem R136a1.of {name : String} {P : Prop} (h : P) : R136a1 name P := h

/-- **The token encodes and decodes exactly**: the token of `P` holds exactly when `P` does. -/
theorem R136a1.iff {name : String} {P : Prop} : R136a1 name P ↔ P := Iff.rfl

/-- **A token of a token is the token** (DMP.DMP): wrapping twice decodes to wrapping once. -/
theorem R136a1.idem {name name' : String} {P : Prop} : R136a1 name (R136a1 name' P) ↔ R136a1 name' P := Iff.rfl

end Arsenal
