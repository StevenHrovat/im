/-
The explanation mechanism: k by k tables of proofs, on Lean's kernel alone.
Released under the Apache License 2.0.
-/

/-!
# The explanation mechanism: k by k tables of proofs

A system is `k` parts. A **table** says, for each pair, whether the row proves the column (`true` is `+`). Indices are natural numbers
and only the first `k` count, so a table for `k` parts is also one for `k + 1`: a part is added by naming one more index, and nothing
already stated about the first `k` changes.

* **Every cell `+`** (`AllPlus`). **Extensibility** (`allPlus_succ_iff`): `k + 1` parts are all `+` exactly when the first `k` are
  and the new part's row, column and own cell are, so nothing proven is checked again; the count of new cells, `2k + 1`, is
  arithmetic (`new_cells`).
* **Derivation** (`comp`, `step`, `derive`): the row proves a part that proves the column. A derived cell always has its chain
  (`chain_of_comp`, `step_sound`), after any number of steps (`derive_sound`: every derived cell is reached by a chain of cells of
  the table), and every chain gives a derived cell (`comp_of_chain`). On an all-`+` table a step adds nothing (`step_eq_of_allPlus`).
  That a derived cell is an explanation and not a proof is the first author's reading, not a theorem here: a derived cell is a `true`
  like any other.
* **The `·` cells** (`Eff`, `allPlus_eff_iff`): where the row does not use the column the cell reflects positively; where it does,
  the proof must be there. Every cell of the effective table is `+` exactly when every used cell is proven.
* **The `.` boundary is a DAG** (`Earlier`, `derive_irrefl`): when every use points to an earlier part, no chain of uses returns to
  where it started, at any length.
* **The parts measured on 2026-11-25** (`versionUses`, `repoUses`): by version, the uses of DMP, Gravity and IM form a DAG
  (`versions_dag`) and every use is proven (`versions_explained`); collapsed to repositories, IM and Gravity use each other
  (`repos_cycle`, `repos_not_dag`). A cycle of repositories is a DAG of versions; that the two never exist at the same time is
  the first author's reading. DMP uses
  nothing and is included by every other part (`dmp_only_included`).
* **The drafts, a library transitive to G0** (`draftUses`): each draft grows from the one before, so the drafts form a DAG however
  many there are (`drafts_dag`, `drafts_no_return`), Draft 6 reaches Draft 4 through Draft 5 (`draft6_reaches_g0`), and in a library
  of eight drafts every later draft reaches G0 (`every_draft_reaches_g0`).

The facts about the measured tables are decided by the kernel's evaluation; the general facts are proved from Lean's core lemmas.
-/

namespace ArsenalCore.Matrix

/-- A **table**: `M i j` says whether part `i` proves part `j`. -/
abbrev Table := Nat → Nat → Bool

/-- **Every cell `+`** among the first `k` parts. -/
def AllPlus (k : Nat) (M : Table) : Prop := ∀ i, i < k → ∀ j, j < k → M i j = true

instance (k : Nat) (M : Table) : Decidable (AllPlus k M) := by
  unfold AllPlus
  infer_instance

/-! ## Extensibility -/

/-- **Adding a part**: `k + 1` parts are all `+` exactly when the first `k` are, and the new part's row, its column and its own cell
are. Nothing already proven about the first `k` is checked again. -/
theorem allPlus_succ_iff (k : Nat) (M : Table) :
    AllPlus (k + 1) M ↔
      AllPlus k M ∧ (∀ j, j < k → M k j = true) ∧ (∀ i, i < k → M i k = true) ∧ M k k = true := by
  constructor
  · intro h
    exact ⟨fun i hi j hj => h i (by omega) j (by omega), fun j hj => h k (by omega) j (by omega),
      fun i hi => h i (by omega) k (by omega), h k (by omega) k (by omega)⟩
  · intro ⟨h0, hr, hc, hd⟩ i hi j hj
    by_cases hik : i < k
    · by_cases hjk : j < k
      · exact h0 i hik j hjk
      · have e : j = k := by omega
        rw [e]; exact hc i hik
    · have e : i = k := by omega
      rw [e]
      by_cases hjk : j < k
      · exact hr j hjk
      · have e' : j = k := by omega
        rw [e']; exact hd

/-- **The cost of a new part**: `2k + 1` cells, its row, its column and its own. -/
theorem new_cells (k : Nat) : (k + 1) * (k + 1) = k * k + (2 * k + 1) := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  omega

/-! ## Derivation -/

/-- **One derivation step between two tables**: the row proves some part that proves the column. -/
def comp (k : Nat) (A B : Table) : Table := fun i j => (List.range k).any (fun l => A i l && B l j)

/-- **Every chain gives a derived cell.** -/
theorem comp_of_chain {k : Nat} {A B : Table} {i l j : Nat} (hl : l < k) (h1 : A i l = true) (h2 : B l j = true) :
    comp k A B i j = true := by
  unfold comp
  rw [List.any_eq_true]
  exact ⟨l, List.mem_range.mpr hl, by rw [h1, h2]; rfl⟩

/-- **Every derived cell has its chain**: the explanation is always there. -/
theorem chain_of_comp {k : Nat} {A B : Table} {i j : Nat} (h : comp k A B i j = true) :
    ∃ l, l < k ∧ A i l = true ∧ B l j = true := by
  unfold comp at h
  rw [List.any_eq_true] at h
  obtain ⟨l, hl, h'⟩ := h
  rw [Bool.and_eq_true] at h'
  exact ⟨l, List.mem_range.mp hl, h'.1, h'.2⟩

/-- **One step of derivation on a table**: a cell, or a chain through one part. -/
def step (k : Nat) (A : Table) : Table := fun i j => A i j || comp k A A i j

/-- **`n` steps.** -/
def derive (k : Nat) (A : Table) : Nat → Table
  | 0 => A
  | n + 1 => step k (derive k A n)

/-- A step keeps every cell it had. -/
theorem le_step {k : Nat} {A : Table} {i j : Nat} (h : A i j = true) : step k A i j = true := by
  unfold step; rw [h]; rfl

/-- **A step's new cells are explained**: a cell of the step is a cell of the table, or a chain through one part. -/
theorem step_sound {k : Nat} {A : Table} {i j : Nat} (h : step k A i j = true) :
    A i j = true ∨ ∃ l, l < k ∧ A i l = true ∧ A l j = true := by
  unfold step at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (chain_of_comp h)

/-- **On an all-`+` table a step adds nothing.** (That a derived cell explains and does not prove is the first author's reading.) -/
theorem step_eq_of_allPlus {k : Nat} {A : Table} (h : AllPlus k A) :
    ∀ i, i < k → ∀ j, j < k → step k A i j = A i j := by
  intro i hi j hj
  rw [h i hi j hj]
  exact le_step (h i hi j hj)

/-- **A chain of cells**: the row reaches the column through parts below `k`, each link a cell of the table. -/
inductive Reach (k : Nat) (A : Table) : Nat → Nat → Prop
  | edge {i j : Nat} : A i j = true → Reach k A i j
  | trans {i l j : Nat} : l < k → Reach k A i l → Reach k A l j → Reach k A i j

/-- **Every derived cell is reached by a chain**, after any number of steps: derivation adds a cell only along chains of cells
already in the table. -/
theorem derive_sound {k : Nat} {A : Table} : ∀ n i j, derive k A n i j = true → Reach k A i j
  | 0, _, _, h => Reach.edge h
  | n + 1, i, j, h => by
    rcases step_sound h with h1 | ⟨l, hl, h1, h2⟩
    · exact derive_sound n i j h1
    · exact Reach.trans hl (derive_sound n i l h1) (derive_sound n l j h2)

/-! ## The `·` cells and the `.` boundary -/

/-- **The effective table**: where the row does not use the column (`U i j = false`) the cell reflects positively; where it uses it,
the cell is the proof `P i j`. -/
def Eff (U P : Table) : Table := fun i j => !U i j || P i j

/-- **Every effective cell is `+` exactly when every used cell is proven.** -/
theorem allPlus_eff_iff (k : Nat) (U P : Table) :
    AllPlus k (Eff U P) ↔ ∀ i, i < k → ∀ j, j < k → U i j = true → P i j = true := by
  constructor
  · intro h i hi j hj hu
    have := h i hi j hj
    unfold Eff at this
    rw [hu] at this
    exact this
  · intro h i hi j hj
    unfold Eff
    cases hu : U i j
    · rfl
    · rw [h i hi j hj hu]; rfl

/-- **A DAG certificate**: every use points to an earlier part. -/
def Earlier (k : Nat) (U : Table) : Prop := ∀ i, i < k → ∀ j, j < k → U i j = true → j < i

instance (k : Nat) (U : Table) : Decidable (Earlier k U) := by
  unfold Earlier
  infer_instance

/-- A step of derivation keeps the certificate on the parts. -/
theorem earlier_step {k : Nat} {U : Table} (h : Earlier k U) : Earlier k (step k U) := by
  intro i hi j hj hs
  rcases step_sound hs with hu | ⟨l, hl, h1, h2⟩
  · exact h i hi j hj hu
  · have a := h i hi l hl h1
    have b := h l hl j hj h2
    omega

/-- Every number of steps keeps it. -/
theorem earlier_derive {k : Nat} {U : Table} (h : Earlier k U) : ∀ n, Earlier k (derive k U n)
  | 0 => h
  | n + 1 => earlier_step (earlier_derive h n)

/-- **No chain of uses returns** to where it started, at any length: the `.` boundary is a DAG. -/
theorem derive_irrefl {k : Nat} {U : Table} (h : Earlier k U) (n : Nat) : ∀ i, i < k → derive k U n i i = false := by
  intro i hi
  cases hd : derive k U n i i
  · rfl
  · have := earlier_derive h n i hi i hi hd
    omega

/-! ## The parts measured on 2026-11-25 -/

/-- **By version**: 0 DMP `1370dc0` (0.9.6), 1 DMP `4400cce` (0.9.9), 2 Gravity `4ec1131`, 3 IM `f8baf3d`, 4 Gravity `db03d05`.
Gravity `4ec1131` holds DMP `1370dc0`; IM `f8baf3d` holds DMP `1370dc0` and Gravity `4ec1131`; Gravity `db03d05` holds DMP
`4400cce` and pins IM `f8baf3d`. -/
def versionUses : Table := fun i j =>
  match i, j with
  | 2, 0 | 3, 0 | 3, 2 | 4, 1 | 4, 3 => true
  | _, _ => false

/-- **The proofs measured on 2026-11-25**: each use proven (a held copy rebuilt byte for byte from its commit, or a pinned commit
fetched by its id and the id recomputed; the copy of DMP inside Gravity `4ec1131` hashes to its pin), and each current part's own round
trip (IM, Gravity `db03d05`). -/
def versionProofs : Table := fun i j =>
  match i, j with
  | 2, 0 | 3, 0 | 3, 2 | 4, 1 | 4, 3 | 3, 3 | 4, 4 => true
  | _, _ => false

/-- **By version the uses form a DAG**: every use points to an earlier version. -/
theorem versions_dag : Earlier 5 versionUses := by decide

/-- **Every used cell is proven**, so the effective 5 by 5 table is all `+`. -/
theorem versions_explained : AllPlus 5 (Eff versionUses versionProofs) := by decide

/-- **No chain of uses returns**, at any length. -/
theorem versions_no_return (n : Nat) : ∀ i, i < 5 → derive 5 versionUses n i i = false :=
  derive_irrefl versions_dag n

/-- **A derived cell**: today's Gravity reaches DMP `1370dc0` through IM, which it does not use directly. -/
theorem gravity_reaches_dmp_through_im : versionUses 4 0 = false ∧ derive 5 versionUses 1 4 0 = true := by decide

/-- **By repository**: 0 DMP, 1 Gravity, 2 IM. -/
def repoUses : Table := fun i j =>
  match i, j with
  | 1, 0 | 2, 0 | 2, 1 | 1, 2 => true
  | _, _ => false

/-- **Collapsed to repositories, IM and Gravity use each other.** -/
theorem repos_cycle : repoUses 1 2 = true ∧ repoUses 2 1 = true := by decide

/-- **So the repositories are not a DAG**; the versions are (`versions_dag`). The first author reads this as the two never existing
at the same time. -/
theorem repos_not_dag : ¬ Earlier 3 repoUses := by decide

/-- **DMP states only inclusion**: by repository, DMP uses nothing (its row is empty) and every other part includes it. -/
theorem dmp_only_included : (∀ j, j < 3 → repoUses 0 j = false) ∧ repoUses 1 0 = true ∧ repoUses 2 0 = true := by decide

/-! ## The drafts: a library transitive to G0 -/

/-- **The drafts as parts**: Draft `4 + i` is part `i`, and each grows from the one before it (part `i + 1` uses part `i`); part 0,
Draft 4, is G0. -/
def draftUses : Table := fun i j => decide (i = j + 1)

/-- **Grown from the one before**: every use points to an earlier draft, so the drafts form a DAG, however many there are. -/
theorem drafts_dag (k : Nat) : Earlier k draftUses := by
  intro i _ j _ h
  have := of_decide_eq_true h
  omega

/-- **Draft 6 reaches G0 through Draft 5**: it does not grow from Draft 4 directly, yet one derivation step reaches it. -/
theorem draft6_reaches_g0 : draftUses 2 0 = false ∧ derive 3 draftUses 1 2 0 = true := by decide

/-- **A longer library**: with eight drafts (Draft 4 to Draft 11), three derivation steps reach G0 from every later draft. -/
theorem every_draft_reaches_g0 : ∀ i, i < 8 → 0 < i → derive 8 draftUses 3 i 0 = true := by decide +kernel

/-- **No draft reaches itself**: the library never returns to where it started, at any number of steps and drafts. -/
theorem drafts_no_return (k n : Nat) : ∀ i, i < k → derive k draftUses n i i = false :=
  derive_irrefl (drafts_dag k) n

end ArsenalCore.Matrix
