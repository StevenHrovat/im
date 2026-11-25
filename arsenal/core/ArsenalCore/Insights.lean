/-
The first author's Insights: no fewer than 8 bits single out one configuration of a byte, and the table of the Insights' references,
settled. On Lean's kernel alone.
Released under the Apache License 2.0.
-/
import ArsenalCore.Optimizer

/-!
# Insights: eight, and their references

Gravity's Draft 6, R.12l. The first author's reading: the Insights recorded on DMP's pull request #25 reduce to no fewer than 8, which
makes the record impossible to reconstruct from any other configuration in exactly the same way. The exact parts proved here:

* **0ne1, the pigeonhole** (`«0ne1»`, the first author's name for it in the logic): an injective map from `n` places into `m` values
  needs `n ≤ m`. Proved by induction, no library.
* **Eight bits, no fewer** (`bits_single_out_iff`): `2^8 = 256` configurations can be told apart by `k` bits exactly when `k ≥ 8`;
  seven bits give `128` values, so two configurations would look the same (`seven_bits_collide`).
* **The Insights' references** (`insightUses`): the eight Insights in time order, a use where an Insight's text refers to an earlier
  one. The table is a DAG (`insights_dag`) and settled: the optimizer removes none of its uses (`insights_settled`), and it removes
  Insights never, only uses, so all eight stay. Which Insight refers to which is read from their texts; that reading is the input.

That the eight are logically independent, so that they are eight independent bits, is the first author's premise, not proved here.
-/

namespace ArsenalCore.Insights

open ArsenalCore.Matrix

/-- **0ne1, the pigeonhole**: an injective map from the first `n` naturals into the first `m` needs `n ≤ m`. -/
theorem «0ne1» : ∀ (n m : Nat) (f : Nat → Nat), (∀ i, i < n → f i < m) →
    (∀ i j, i < n → j < n → f i = f j → i = j) → n ≤ m
  | 0, _, _, _, _ => Nat.zero_le _
  | n + 1, m, f, hb, hi => by
    have ha : f n < m := hb n (by omega)
    let g : Nat → Nat := fun i => if f i < f n then f i else f i - 1
    have hne : ∀ i, i < n → f i ≠ f n := fun i h e => by have := hi i n (by omega) (by omega) e; omega
    have hgb : ∀ i, i < n → g i < m - 1 := by
      intro i h
      have := hb i (by omega); have := hne i h
      show (if f i < f n then f i else f i - 1) < m - 1
      split <;> omega
    have hgi : ∀ i j, i < n → j < n → g i = g j → i = j := by
      intro i j h1 h2 e
      have := hne i h1; have := hne j h2
      have e' : (if f i < f n then f i else f i - 1) = (if f j < f n then f j else f j - 1) := e
      have key : f i = f j := by split at e' <;> split at e' <;> omega
      exact hi i j (by omega) (by omega) key
    have := «0ne1» n (m - 1) g hgb hgi
    omega

/-- Configurations of `k` bits can be told apart from the `256` of a byte exactly when there are at least `256` of them. -/
def SinglesOut (k : Nat) : Prop :=
  ∃ f : Nat → Nat, (∀ i, i < 256 → f i < 2 ^ k) ∧ (∀ i j, i < 256 → j < 256 → f i = f j → i = j)

/-- **Eight bits, no fewer**: `k` bits single out every one of the `256` configurations of a byte exactly when `k ≥ 8`. -/
theorem bits_single_out_iff (k : Nat) : SinglesOut k ↔ 8 ≤ k := by
  constructor
  · intro ⟨f, hb, hi⟩
    have h := «0ne1» 256 (2 ^ k) f hb hi
    by_cases hk : 8 ≤ k
    · exact hk
    · exfalso
      have : 2 ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
      have : (2 : Nat) ^ 7 = 128 := by decide
      omega
  · intro hk
    refine ⟨fun i => i, fun i h => ?_, fun _ _ _ _ e => e⟩
    show i < 2 ^ k
    have : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    have : (2 : Nat) ^ 8 = 256 := by decide
    omega

/-- **Seven bits collide**: no map of the `256` configurations into `7` bits tells them all apart. -/
theorem seven_bits_collide : ¬ SinglesOut 7 := fun h => by
  have := (bits_single_out_iff 7).mp h
  omega

/-! ## The Insights' references -/

/-- **The eight Insights**, in time order (DMP#25, comments read 2026-11-25): 0 at 2026-10-28 14:43Z, 1 at 15:00Z, 2 at 15:33Z, 3 at
16:06Z, 4 at 17:46Z, 5 at 2026-10-29 13:26Z, 6 at 17:57Z, 7 at 19:58Z. A use where an Insight's text refers to an earlier one:
2 corrects 1 ("Correction + new Insight", on what crosses a boundary); 4 says why the ODP of 0 is needed; 5 builds on the entropy of 2;
6 revisits "my Insight on QC", which is 1; 7 states the FSC's point that 5 introduced. -/
def insightUses : Table := fun i j =>
  match i, j with
  | 2, 1 | 4, 0 | 5, 2 | 6, 1 | 7, 5 => true
  | _, _ => false

/-- **The references form a DAG**: every Insight refers only to earlier ones. -/
theorem insights_dag : Earlier 8 insightUses := by decide

/-- **And the table is settled**: the optimizer removes none of its uses, and it never removes an Insight. -/
theorem insights_settled : Settled 8 insightUses := by decide

end ArsenalCore.Insights
