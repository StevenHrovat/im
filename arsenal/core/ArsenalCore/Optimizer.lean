/-
The optimizer, the mirror of the explanation mechanism: the transitive reduction of a DAG, on Lean's kernel alone.
Released under the Apache License 2.0.
-/
import ArsenalCore.Matrix

/-!
# The optimizer: the transitive reduction of a DAG

The explanation mechanism (`ArsenalCore.Matrix`) builds up: a part is added, a cell is derived. The **optimizer** is its mirror: it
removes every use that is already included through another chain. For each use the question `?` is asked (is this use needed?),
and the use is removed exactly when it is shown to be unnecessary by `.` (it is already included through another part). What remains is
the **transitive reduction** of the DAG (Aho, Garey and Ullman 1972). "DAG" here is `Earlier`: the parts are numbered so that every
use points to an earlier part, which every DAG allows (a topological order), so the general facts hold for every DAG up to
renumbering.

* **Chains of bounded length** (`path`, `close`): `path k A n i j` says a chain of at most `n` uses leads from `i` to `j` through parts
  below `k`; `close k A i j` is `path` with `i` steps, which is every chain in a DAG (`path_bound`), and chains join (`close_trans`).
* **The optimizer** (`redundant`, `reduce`): a use is redundant when the row reaches the column through another part it uses; the
  reduction keeps exactly the uses that are not.
* **What it keeps** (`close_reduce`): on a DAG the reduction reaches exactly what the table reaches, so every derivation, and with it
  every explanation, survives.
* **Settled** (`Settled`): a table is settled when optimizing it changes nothing, that is, when the compiled table and the optimized
  one are the same. On a DAG, optimizing once settles (`reduce_settled`, `reduce_idem`).
* **Nothing more can go** (`reduce_minimal`): removing any kept use loses a derivation.
* **One settled form** (`settled_unique`, `reduce_unique`): two settled DAGs that reach the same parts are the same table, so the
  reduction is the only settled table with the original's reach. This is the uniqueness of the transitive reduction of a DAG (Aho,
  Garey and Ullman 1972), proved here on the kernel alone.
* **The parts measured on 2026-11-25**: by version, IM `f8baf3d`'s direct use of DMP `1370dc0` is redundant, since it also holds
  Gravity `4ec1131`, which holds that DMP (`im_use_of_dmp_redundant`); so the version table is not settled
  (`versions_not_settled`) and its reduction removes exactly that use (`versions_reduced`). The drafts are settled however many
  there are (`drafts_settled`). On the repository cycle, which is not a DAG, the optimizer removes both uses of DMP and loses it
  (`repos_reduce_loses_dmp`): the optimizer needs the DAG.

That compiled = optimized is the condition for the setting, and so the system, to exist, and that the optimizer is the Arsenal's
mirror, are the first author's readings; the theorems here are what they rest on.
-/

namespace ArsenalCore.Matrix

/-! ## Chains of bounded length -/

/-- **A chain of at most `n` uses** from `i` to `j`, each intermediate part below `k`. -/
def path (k : Nat) (A : Table) : Nat → Table
  | 0 => fun _ _ => false
  | n + 1 => fun i j => (List.range k).any (fun l => A i l && (l == j || path k A n l j))

/-- **Every chain**, in a DAG: a chain from `i` has at most `i` uses (`path_bound`). -/
def close (k : Nat) (A : Table) : Table := fun i j => path k A i i j

theorem path_succ_iff {k : Nat} {A : Table} {n i j : Nat} :
    path k A (n + 1) i j = true ↔ ∃ l, l < k ∧ A i l = true ∧ (l = j ∨ path k A n l j = true) := by
  show (List.range k).any _ = true ↔ _
  rw [List.any_eq_true]
  constructor
  · intro ⟨l, hl, h⟩
    rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    exact ⟨l, List.mem_range.mp hl, h.1, h.2⟩
  · intro ⟨l, hl, h1, h2⟩
    refine ⟨l, List.mem_range.mpr hl, ?_⟩
    rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    exact ⟨h1, h2⟩

/-- A longer bound keeps every chain. -/
theorem path_succ {k : Nat} {A : Table} : ∀ {n i j : Nat}, path k A n i j = true → path k A (n + 1) i j = true
  | 0, _, _, h => by simp [path] at h
  | n + 1, i, j, h => by
    obtain ⟨l, hl, h1, h2⟩ := path_succ_iff.mp h
    refine path_succ_iff.mpr ⟨l, hl, h1, ?_⟩
    rcases h2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (path_succ h2)

theorem path_mono {k : Nat} {A : Table} {n m i j : Nat} (hnm : n ≤ m) (h : path k A n i j = true) : path k A m i j = true := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact path_succ ih

/-- **A use is a chain.** -/
theorem path_of_use {k : Nat} {A : Table} {i j : Nat} (hj : j < k) (h : A i j = true) : path k A 1 i j = true :=
  path_succ_iff.mpr ⟨j, hj, h, Or.inl rfl⟩

/-- **Chains join.** -/
theorem path_trans {k : Nat} {A : Table} : ∀ {n m i l j : Nat},
    path k A n i l = true → path k A m l j = true → path k A (n + m) i j = true
  | 0, _, _, _, _, h, _ => by simp [path] at h
  | n + 1, m, i, l, j, h1, h2 => by
    obtain ⟨l', hl', u, h⟩ := path_succ_iff.mp h1
    have e : n + 1 + m = (n + m) + 1 := by omega
    rw [e]
    refine path_succ_iff.mpr ⟨l', hl', u, Or.inr ?_⟩
    rcases h with h | h
    · subst h; exact path_mono (by omega) h2
    · exact path_trans h h2

/-- **Chains stay among the parts and go down**, in a DAG. -/
theorem path_lt {k : Nat} {A : Table} (hA : Earlier k A) : ∀ {n i j : Nat}, i < k → path k A n i j = true → j < i
  | 0, _, _, _, h => by simp [path] at h
  | n + 1, i, j, hi, h => by
    obtain ⟨l, hl, u, h⟩ := path_succ_iff.mp h
    have a := hA i hi l hl u
    rcases h with h | h
    · omega
    · have := path_lt hA hl h; omega

/-- **Unfolding `close`**: a chain from `i` starts with a use. -/
theorem close_cases {k : Nat} {A : Table} {i j : Nat} (h : close k A i j = true) :
    ∃ l, l < k ∧ A i l = true ∧ (l = j ∨ path k A (i - 1) l j = true) := by
  unfold close at h
  cases i with
  | zero => simp [path] at h
  | succ p => exact path_succ_iff.mp h

theorem close_intro {k : Nat} {A : Table} {i l j : Nat} (hi : 0 < i) (hl : l < k) (u : A i l = true)
    (h : l = j ∨ path k A (i - 1) l j = true) : close k A i j = true := by
  unfold close
  cases i with
  | zero => omega
  | succ p => exact path_succ_iff.mpr ⟨l, hl, u, h⟩

/-- **A chain from `i` has at most `i` uses**, in a DAG: every chain is in `close`. -/
theorem path_bound {k : Nat} {A : Table} (hA : Earlier k A) : ∀ {n i j : Nat}, i < k → path k A n i j = true → close k A i j = true
  | 0, _, _, _, h => by simp [path] at h
  | n + 1, i, j, hi, h => by
    obtain ⟨l, hl, u, h⟩ := path_succ_iff.mp h
    have a := hA i hi l hl u
    refine close_intro (by omega) hl u ?_
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (path_mono (by omega) (path_bound hA hl h))

theorem close_of_use {k : Nat} {A : Table} (hA : Earlier k A) {i j : Nat} (hi : i < k) (hj : j < k) (h : A i j = true) :
    close k A i j = true :=
  path_bound hA hi (path_of_use hj h)

theorem close_lt {k : Nat} {A : Table} (hA : Earlier k A) {i j : Nat} (hi : i < k) (h : close k A i j = true) : j < i :=
  path_lt hA hi h

/-- **No part reaches itself**, in a DAG. -/
theorem close_irrefl {k : Nat} {A : Table} (hA : Earlier k A) {i : Nat} (hi : i < k) : close k A i i = false := by
  cases h : close k A i i
  · rfl
  · have := close_lt hA hi h; omega

/-- **Chains join**, in a DAG. -/
theorem close_trans {k : Nat} {A : Table} (hA : Earlier k A) {i l j : Nat} (hi : i < k)
    (h1 : close k A i l = true) (h2 : close k A l j = true) : close k A i j = true :=
  path_bound hA hi (path_trans h1 h2)

/-- **A chain of a smaller table is a chain of the larger.** -/
theorem path_sub {k : Nat} {A B : Table} (hAB : ∀ i j, A i j = true → B i j = true) :
    ∀ {n i j : Nat}, path k A n i j = true → path k B n i j = true
  | 0, _, _, h => by simp [path] at h
  | n + 1, _, _, h => by
    obtain ⟨l, hl, u, h⟩ := path_succ_iff.mp h
    refine path_succ_iff.mpr ⟨l, hl, hAB _ _ u, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (path_sub hAB h)

/-- A smaller table of a DAG is a DAG. -/
theorem earlier_sub {k : Nat} {A B : Table} (hB : Earlier k B) (hAB : ∀ i j, A i j = true → B i j = true) : Earlier k A :=
  fun i hi j hj h => hB i hi j hj (hAB i j h)

/-- **Chains in a table are the chains of the explanation mechanism** (`Reach`). -/
theorem reach_of_path {k : Nat} {A : Table} : ∀ {n i j : Nat}, path k A n i j = true → Reach k A i j
  | 0, _, _, h => by simp [path] at h
  | n + 1, _, _, h => by
    obtain ⟨l, hl, u, h⟩ := path_succ_iff.mp h
    rcases h with h | h
    · subst h; exact Reach.edge u
    · exact Reach.trans hl (Reach.edge u) (reach_of_path h)

/-! ## The optimizer -/

/-- **`?` answered by `.`**: the use of `j` by `i` is redundant when `i` uses another part that already reaches `j`. -/
def redundant (k : Nat) (A : Table) : Table := fun i j => (List.range k).any (fun l => A i l && close k A l j)

/-- **The optimizer**: keep exactly the uses that are not redundant. -/
def reduce (k : Nat) (A : Table) : Table := fun i j => A i j && !redundant k A i j

/-- **Settled**: optimizing changes nothing; the compiled table and the optimized one are the same. -/
def Settled (k : Nat) (A : Table) : Prop := ∀ i, i < k → ∀ j, j < k → reduce k A i j = A i j

instance (k : Nat) (A : Table) : Decidable (Settled k A) := by
  unfold Settled
  infer_instance

theorem redundant_iff {k : Nat} {A : Table} {i j : Nat} :
    redundant k A i j = true ↔ ∃ l, l < k ∧ A i l = true ∧ close k A l j = true := by
  unfold redundant
  rw [List.any_eq_true]
  constructor
  · intro ⟨l, hl, h⟩
    rw [Bool.and_eq_true] at h
    exact ⟨l, List.mem_range.mp hl, h.1, h.2⟩
  · intro ⟨l, hl, h1, h2⟩
    exact ⟨l, List.mem_range.mpr hl, by rw [h1, h2]; rfl⟩

theorem reduce_iff {k : Nat} {A : Table} {i j : Nat} :
    reduce k A i j = true ↔ A i j = true ∧ redundant k A i j = false := by
  unfold reduce
  rw [Bool.and_eq_true, Bool.not_eq_true']

/-- The optimizer only removes. -/
theorem reduce_le {k : Nat} {A : Table} {i j : Nat} (h : reduce k A i j = true) : A i j = true :=
  (reduce_iff.mp h).1

theorem earlier_reduce {k : Nat} {A : Table} (hA : Earlier k A) : Earlier k (reduce k A) :=
  earlier_sub hA fun _ _ => reduce_le

/-- A step of the proof of `close_reduce`: if every use within `d` is reached in the reduction, so is every chain within `d`. -/
private theorem chain_in_reduce {k : Nat} {A : Table} (hA : Earlier k A) (d : Nat)
    (hu : ∀ i j, i < k → j < k → i ≤ j + d → A i j = true → close k (reduce k A) i j = true) :
    ∀ {n i j : Nat}, i < k → i ≤ j + d → path k A n i j = true → close k (reduce k A) i j = true
  | 0, _, _, _, _, h => by simp [path] at h
  | n + 1, i, j, hi, hd, h => by
    obtain ⟨l, hl, u, h⟩ := path_succ_iff.mp h
    have a := hA i hi l hl u
    rcases h with h | h
    · subst h; exact hu i l hi hl (by omega) u
    · have b := path_lt hA hl h
      exact close_trans (earlier_reduce hA) hi (hu i l hi hl (by omega) u) (chain_in_reduce hA d hu hl (by omega) h)

/-- The other step: every use whose two parts lie within `d` of each other is reached in the reduction. -/
private theorem use_in_reduce {k : Nat} {A : Table} (hA : Earlier k A) : ∀ d i j, i < k → j < k → i ≤ j + d →
    A i j = true → close k (reduce k A) i j = true
  | 0, i, j, hi, hj, hd, u => by have := hA i hi j hj u; omega
  | d + 1, i, j, hi, hj, hd, u => by
    cases hr : redundant k A i j
    · exact close_of_use (earlier_reduce hA) hi hj (reduce_iff.mpr ⟨u, hr⟩)
    · obtain ⟨l, hl, u1, c⟩ := redundant_iff.mp hr
      have a := hA i hi l hl u1
      have b := close_lt hA hl c
      exact close_trans (earlier_reduce hA) hi (use_in_reduce hA d i l hi hl (by omega) u1)
        (chain_in_reduce hA d (use_in_reduce hA d) hl (by omega) c)

/-- **The optimizer keeps every derivation**: on a DAG the reduction reaches exactly what the table reaches. -/
theorem close_reduce {k : Nat} {A : Table} (hA : Earlier k A) {i j : Nat} (hi : i < k) :
    close k (reduce k A) i j = close k A i j := by
  cases h : close k A i j
  · cases h' : close k (reduce k A) i j
    · rfl
    · have h2 : close k A i j = true := path_sub (A := reduce k A) (B := A) (fun _ _ => reduce_le) h'
      rw [h] at h2; exact h2.symm
  · exact chain_in_reduce hA i (use_in_reduce hA i) hi (by omega) h

/-- **Optimizing once settles.** -/
theorem reduce_settled {k : Nat} {A : Table} (hA : Earlier k A) : Settled k (reduce k A) := by
  intro i hi j hj
  show (reduce k A i j && !redundant k (reduce k A) i j) = reduce k A i j
  cases hr : reduce k A i j
  · rfl
  · cases h : redundant k (reduce k A) i j
    · rfl
    · exfalso
      obtain ⟨l, hl, u, c⟩ := redundant_iff.mp h
      rw [close_reduce hA hl] at c
      have : redundant k A i j = true := redundant_iff.mpr ⟨l, hl, reduce_le u, c⟩
      rw [(reduce_iff.mp hr).2] at this; exact Bool.false_ne_true this

/-- **Optimizing twice is optimizing once.** -/
theorem reduce_idem {k : Nat} {A : Table} (hA : Earlier k A) :
    ∀ i, i < k → ∀ j, j < k → reduce k (reduce k A) i j = reduce k A i j :=
  reduce_settled hA

/-- **Nothing more can go**: removing any kept use loses a derivation. -/
theorem reduce_minimal {k : Nat} {A : Table} (hA : Earlier k A) {i j : Nat} (hi : i < k) (h : reduce k A i j = true) :
    close k (fun a b => reduce k A a b && !(a == i && b == j)) i j = false := by
  cases hc : close k (fun a b => reduce k A a b && !(a == i && b == j)) i j
  · rfl
  · exfalso
    obtain ⟨l, hl, u, hlj⟩ := close_cases hc
    rw [Bool.and_eq_true, Bool.not_eq_true'] at u
    rcases hlj with e | p
    · subst e; simp at u
    · have p' := path_sub (fun a b hab => by
        simp only [Bool.and_eq_true] at hab; exact reduce_le hab.1) p
      have hi' : 0 < i := by have := hA i hi l hl (reduce_le u.1); omega
      have c := path_bound hA hl p'
      have : redundant k A i j = true := redundant_iff.mpr ⟨l, hl, reduce_le u.1, c⟩
      rw [(reduce_iff.mp h).2] at this; exact Bool.false_ne_true this

/-- **One settled form**: two settled DAGs that reach the same parts are the same table. -/
theorem settled_unique {k : Nat} {A B : Table} (hA : Earlier k A) (hB : Earlier k B) (sA : Settled k A) (sB : Settled k B)
    (hc : ∀ i, i < k → ∀ j, close k A i j = close k B i j) : ∀ i, i < k → ∀ j, j < k → A i j = B i j := by
  have one : ∀ {A B : Table}, Earlier k A → Earlier k B → Settled k A → (∀ i, i < k → ∀ j, close k A i j = close k B i j) →
      ∀ i, i < k → ∀ j, j < k → A i j = true → B i j = true := by
    intro A B hA hB sA hc i hi j hj u
    have cB : close k B i j = true := by rw [← hc i hi j]; exact close_of_use hA hi hj u
    obtain ⟨l, hl, v, h⟩ := close_cases cB
    rcases h with e | p
    · subst e; exact v
    · exfalso
      have clj : close k A l j = true := by rw [hc l hl j]; exact path_bound hB hl p
      have cil : close k A i l = true := by rw [hc i hi l]; exact close_of_use hB hi hl v
      obtain ⟨m, hm, w, h2⟩ := close_cases cil
      have cmj : close k A m j = true := by
        rcases h2 with e | q
        · subst e; exact clj
        · exact close_trans hA hm (path_bound hA hm q) clj
      have : redundant k A i j = true := redundant_iff.mpr ⟨m, hm, w, cmj⟩
      have s := sA i hi j hj
      unfold reduce at s
      rw [this, u] at s
      exact Bool.false_ne_true s
  intro i hi j hj
  cases hAij : A i j
  · cases hBij : B i j
    · rfl
    · have := one hB hA sB (fun a ha b => (hc a ha b).symm) i hi j hj hBij
      rw [hAij] at this; exact this
  · exact (one hA hB sA hc i hi j hj hAij).symm

/-- **The reduction is the only settled table with the original's reach.** -/
theorem reduce_unique {k : Nat} {A B : Table} (hA : Earlier k A) (hB : Earlier k B) (sB : Settled k B)
    (hc : ∀ i, i < k → ∀ j, close k B i j = close k A i j) : ∀ i, i < k → ∀ j, j < k → B i j = reduce k A i j :=
  settled_unique hB (earlier_reduce hA) sB (reduce_settled hA)
    (fun i hi j => by rw [close_reduce hA hi]; exact hc i hi j)

/-! ## The parts measured on 2026-11-25 -/

/-- **IM `f8baf3d`'s direct use of DMP `1370dc0` is redundant**: it also holds Gravity `4ec1131`, which holds that DMP. -/
theorem im_use_of_dmp_redundant : versionUses 3 0 = true ∧ redundant 5 versionUses 3 0 = true := by decide

/-- **So the version table is not settled.** -/
theorem versions_not_settled : ¬ Settled 5 versionUses := by decide

/-- **The settled version table**: the measured uses without IM's direct use of DMP. -/
def versionsSettled : Table := fun i j =>
  match i, j with
  | 2, 0 | 3, 2 | 4, 1 | 4, 3 => true
  | _, _ => false

/-- **The optimizer removes exactly that use.** -/
theorem versions_reduced : ∀ i, i < 5 → ∀ j, j < 5 → reduce 5 versionUses i j = versionsSettled i j := by decide

/-- **And the result is settled**, reaching every part the measured table reaches. -/
theorem versions_settled : Settled 5 versionsSettled ∧
    ∀ i, i < 5 → ∀ j, j < 5 → close 5 versionsSettled i j = close 5 versionUses i j := by decide

/-- **The drafts are settled**, however many there are: each grows from the one before and from nothing else. -/
theorem drafts_settled (k : Nat) : Settled k draftUses := by
  intro i _ j hj
  unfold reduce
  cases hu : draftUses i j
  · rfl
  · cases hr : redundant k draftUses i j
    · rfl
    · exfalso
      obtain ⟨l, hl, u, c⟩ := redundant_iff.mp hr
      have e1 := of_decide_eq_true hu
      have e2 := of_decide_eq_true u
      have : l = j := by omega
      rw [this, close_irrefl (drafts_dag k) hj] at c
      exact Bool.false_ne_true c

/-- **On the repository cycle the optimizer loses DMP**: each use of DMP is redundant through the other repository, both go, and
nothing reaches DMP any more. The optimizer keeps every derivation only on a DAG (`close_reduce`). -/
theorem repos_reduce_loses_dmp : repoUses 1 0 = true ∧ repoUses 2 0 = true ∧ reduce 3 repoUses 1 0 = false ∧
    reduce 3 repoUses 2 0 = false ∧ close 3 (reduce 3 repoUses) 1 0 = false ∧ close 3 (reduce 3 repoUses) 2 0 = false := by
  decide

end ArsenalCore.Matrix
