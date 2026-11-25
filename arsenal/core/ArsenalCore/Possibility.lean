/-
The possibility space: a question, its two answers and the right angle, on Lean's kernel alone.
Released under the Apache License 2.0.
-/

/-!
# The possibility space

The exact parts under the first author's reading of Draft 6, "the Possibility Space". The reading itself (a question as a point, its
answer a line that gives it only `+`, the right angle as the direction from the question to its certificate) is the author's; what
is proved here is the arithmetic it rests on, on integer points of the plane, with no library.

* **The right angle `r`** (`r`): the quarter turn `(x, y) ↦ (-y, x)`, multiplication by `i`. Twice is the flip from `+` to `-`
  (`r_r`), four times is nothing (`r_four`). It is a right angle (`dot_r`) of the same length (`norm_r`), and it acts on lines,
  not only on vectors: it commutes with every scaling (`r_smul`), so a line is turned to a line whatever its length.
* **"Is there a right angle?"** (`right_angle_exists`): for every point, yes, by construction, the witness being `r` itself.
* **The sector map** (`center`, `sector`): the centres of the four quadrants of the square of width `+-`, read 1 to 4 as `.`, `r`,
  `.`, `?`. One `r` goes from quadrant 1 to quadrant 2, a second one to quadrant 3 (`r_quadrants`); the path from 1 through 2 to 3
  has its one corner at quadrant 2, the `r` cell, and the corner is a right angle (`corner_at_r`); quadrant 3 is quadrant 1
  flipped (`q3_is_q1_flipped`).
* **A yes/no question has exactly two answers** (`answers_of_idem`): a projector `P` (`P P = P`) can only answer `1` or `0`.
  The projector onto the first axis (`proj`) is one, answering `1` on its line and `0` across it (`proj_answers`).
* **`?` is not `!`** (`every_question_has_an_answer`, `assignment_does_not_decide`): every question has an answer, `+` or `-`,
  but this holds for a question whose answer is `-` as much as for one whose answer is `+`, so assigning `+` and `-` settles
  nothing. In Lean it is `Classical.em`, which rests on `Classical.choice`; a settlement is a proof of the proposition itself.
-/

namespace ArsenalCore.Possibility

/-- A point of the plane with integer coordinates. -/
abbrev Pt := Int × Int

/-- Scaling. -/
def smul (c : Int) (p : Pt) : Pt := (c * p.1, c * p.2)

/-- The flip from `+` to `-`. -/
def neg (p : Pt) : Pt := (-p.1, -p.2)

/-- The inner product. -/
def dot (p q : Pt) : Int := p.1 * q.1 + p.2 * q.2

/-- The squared length. -/
def norm (p : Pt) : Int := dot p p

/-- **The right angle `r`**: the quarter turn, multiplication by `i`. -/
def r (p : Pt) : Pt := (-p.2, p.1)

/-- **Twice `r` is the flip**: `i · i = -1`. -/
theorem r_r (p : Pt) : r (r p) = neg p := rfl

/-- **Four times `r` is nothing.** -/
theorem r_four (p : Pt) : r (r (r (r p))) = p := by
  simp only [r, Int.neg_neg]

/-- **`r` is a right angle.** -/
theorem dot_r (p : Pt) : dot p (r p) = 0 := by
  simp only [dot, r]
  rw [Int.mul_neg, Int.mul_comm p.2 p.1]
  omega

/-- **Of the same length.** -/
theorem norm_r (p : Pt) : norm (r p) = norm p := by
  simp only [norm, dot, r, Int.neg_mul_neg]
  omega

/-- **`r` acts on lines**: it commutes with every scaling. -/
theorem r_smul (c : Int) (p : Pt) : r (smul c p) = smul c (r p) := by
  simp only [r, smul, Int.mul_neg]

/-- **"Is there a right angle?"**: for every point, yes, the witness being `r`. -/
theorem right_angle_exists (p : Pt) : ∃ q, dot p q = 0 ∧ norm q = norm p :=
  ⟨r p, dot_r p, norm_r p⟩

/-! ## The sector map -/

/-- The marks of the sector map. -/
inductive Mark
  | dot
  | r
  | ask
  deriving DecidableEq

/-- **The centres of the quadrants** of the square of width `+-`, at twice their coordinates: quadrant 1 at `(1, 1)`, then counter
clockwise. -/
def center : Nat → Pt
  | 1 => (1, 1)
  | 2 => (-1, 1)
  | 3 => (-1, -1)
  | _ => (1, -1)

/-- **The sector map**, read 1 to 4: `.`, `r`, `.`, `?`. -/
def sector : Nat → Mark
  | 1 => .dot
  | 2 => .r
  | 3 => .dot
  | _ => .ask

theorem sector_reads : [1, 2, 3, 4].map sector = [.dot, .r, .dot, .ask] := rfl

/-- **One `r` per quadrant**: 1 to 2 to 3 to 4 and back to 1. -/
theorem r_quadrants : r (center 1) = center 2 ∧ r (center 2) = center 3 ∧ r (center 3) = center 4 ∧ r (center 4) = center 1 := by
  decide

/-- **Quadrant 3 is quadrant 1 flipped**, two `r` away. -/
theorem q3_is_q1_flipped : center 3 = neg (center 1) ∧ center 3 = r (r (center 1)) := by decide

/-- **The corner at the `r` cell**: the path from quadrant 1 through quadrant 2 to quadrant 3 turns by a right angle, at quadrant 2,
whose mark is `r`. -/
theorem corner_at_r :
    dot ((center 2).1 - (center 1).1, (center 2).2 - (center 1).2) ((center 3).1 - (center 2).1, (center 3).2 - (center 2).2) = 0 ∧
      sector 2 = .r := by
  decide

/-! ## Two answers -/

/-- **A yes/no question has two answers**: a number equal to its own square is `0` or `1`. -/
theorem answers_of_idem (x : Int) (h : x * x = x) : x = 0 ∨ x = 1 := by
  have e : x * (x - 1) = 0 := by rw [Int.mul_sub, Int.mul_one, h, Int.sub_self]
  rcases Int.mul_eq_zero.mp e with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by omega)

/-- **A projector**: onto the first axis. -/
def proj (p : Pt) : Pt := (p.1, 0)

/-- **It is a question**: asking twice is asking once; it answers `1` on its line and `0` across it. -/
theorem proj_answers : (∀ p, proj (proj p) = proj p) ∧ proj (1, 0) = smul 1 (1, 0) ∧ proj (0, 1) = smul 0 (0, 1) :=
  ⟨fun _ => rfl, rfl, rfl⟩

/-! ## `?` is not `!` -/

/-- **Every question has an answer**, `+` or `-` (`Classical.em`, resting on `Classical.choice`). -/
theorem every_question_has_an_answer (p : Prop) : p ∨ ¬ p := Classical.em p

/-- **Assigning `+` and `-` settles nothing**: it holds for a question whose answer is `-` as much as for one whose answer is `+`. -/
theorem assignment_does_not_decide : (True ∨ ¬ True) ∧ (False ∨ ¬ False) ∧ True ∧ ¬ False :=
  ⟨every_question_has_an_answer True, every_question_has_an_answer False, trivial, id⟩

end ArsenalCore.Possibility
