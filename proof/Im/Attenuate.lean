import Im.Laws
/-!
# Attenuation: a token derived from another carries a subset of its kinds

The closure (Closure.lean) decides the shapes. Safety over time, whether a part can ever come to hold a kind it was not granted,
is decidable only under three conditions (Harrison, Ruzzo and Ullman, 1976; Jones, Lipton and Snyder, 1976 and 1977; Sandhu,
1988 and 1992): a closed table of kinds, tokens that only attenuate, and no sentence that grants. The table is closed
(Grammar.lean, `Kind.all`). This file writes the second condition as theorems (docs/findings.md, IF9) and states the third for
the door.

A token is the set of kinds it carries (`Perms`). Attenuation narrows a parent by a caveat: the child carries a kind only when the
parent carries it and the caveat keeps it (`attenuate`), the discipline of Macaroons, Biscuit and SPKI (docs/acknowledgements.md).

- `attenuate_sub`: an attenuated token's kinds are a subset of its parent's.
- `attenuateAll_eq`, `attenuateAll_sub`: a chain of attenuations is the intersection of the root with every caveat, in any order,
  and stays inside the root.
- `Grants.pass_of_attenuated`, `Grants.pass_of_attenuateAll`: what a door passes for attenuated grants it passes for the parents;
  `Grants.refuse_of_attenuateAll`: what the parents' door refuses, every attenuation refuses. Along any chain of attenuations the
  set of passing sentences only shrinks.
- `Grants.attenuate_noGrants`: the empty grant attenuates only to itself; nothing attenuates into authority.
- `decide_is_verdict`: deciding a sentence returns a verdict and nothing else, so no sentence grants (the door has no
  output that is a grant).

What this is not: the C# token code is not proved to implement `attenuate`; as in Laws.lean, which token carries which kind is the
implementation's, and the conformance is the tests' job.
-/
namespace Im

/-- A token's permissions: which kinds it carries. -/
abbrev Perms := Kind → Bool

/-- A token's kinds are among another's. -/
def Perms.Sub (a b : Perms) : Prop := ∀ k, a k = true → b k = true

/-- Attenuation: the child carries a kind only when the parent carries it and the caveat keeps it. -/
def attenuate (parent caveat : Perms) : Perms := fun k => parent k && caveat k

/-- A chain of attenuations from a root, caveat by caveat. -/
def attenuateAll (root : Perms) (cs : List Perms) : Perms := cs.foldl attenuate root

/-- An attenuated token's kinds are a subset of its parent's. -/
theorem attenuate_sub (p c : Perms) : (attenuate p c).Sub p := by
  intro k h
  simp only [attenuate, Bool.and_eq_true] at h
  exact h.1

/-- The caveat bounds the child too. -/
theorem attenuate_sub_caveat (p c : Perms) : (attenuate p c).Sub c := by
  intro k h
  simp only [attenuate, Bool.and_eq_true] at h
  exact h.2

/-- Subset is transitive. -/
theorem Perms.sub_trans {a b c : Perms} (h1 : a.Sub b) (h2 : b.Sub c) : a.Sub c := fun k h => h2 k (h1 k h)

/-- Attenuation keeps the subset order of parents. -/
theorem attenuate_mono {p q : Perms} (h : p.Sub q) (c : Perms) : (attenuate p c).Sub (attenuate q c) := by
  intro k hk
  simp only [attenuate, Bool.and_eq_true] at hk ⊢
  exact ⟨h k hk.1, hk.2⟩

/-- A chain of attenuations is the intersection of the root with every caveat. -/
theorem attenuateAll_eq (root : Perms) (cs : List Perms) (k : Kind) :
    attenuateAll root cs k = (root k && cs.all fun c => c k) := by
  induction cs generalizing root with
  | nil => simp [attenuateAll]
  | cons c cs ih =>
    simp only [attenuateAll, List.foldl_cons] at ih ⊢
    rw [ih (attenuate root c)]
    simp only [attenuate, List.all_cons, Bool.and_assoc]

/-- The order of the caveats does not matter. -/
theorem attenuateAll_perm (root : Perms) {cs cs' : List Perms} (h : cs.Perm cs') (k : Kind) :
    attenuateAll root cs k = attenuateAll root cs' k := by
  rw [attenuateAll_eq, attenuateAll_eq]
  congr 1
  cases hc : cs.all (fun c => c k) <;> cases hc' : cs'.all (fun c => c k) <;> try rfl
  · rw [List.all_eq_true] at hc'
    rw [List.all_eq_false] at hc
    obtain ⟨c, hc1, hc2⟩ := hc
    exact absurd (hc' c (h.mem_iff.1 hc1)) hc2
  · rw [List.all_eq_true] at hc
    rw [List.all_eq_false] at hc'
    obtain ⟨c, hc1, hc2⟩ := hc'
    exact absurd (hc c (h.mem_iff.2 hc1)) hc2

/-- A chain of attenuations stays inside the root. -/
theorem attenuateAll_sub (root : Perms) (cs : List Perms) : (attenuateAll root cs).Sub root := by
  intro k h
  rw [attenuateAll_eq, Bool.and_eq_true] at h
  exact h.1

/-- Both tokens of a sender, attenuated by one caveat each. -/
def Grants.attenuate (g c : Grants) : Grants :=
  ⟨Im.attenuate g.security c.security, Im.attenuate g.operational c.operational⟩

/-- Both tokens, along a chain of caveats. -/
def Grants.attenuateAll (g : Grants) (cs : List Grants) : Grants := cs.foldl Grants.attenuate g

/-- One grant is inside another, token by token. -/
def Grants.Sub (g h : Grants) : Prop := Perms.Sub g.security h.security ∧ Perms.Sub g.operational h.operational

theorem Grants.attenuate_sub (g c : Grants) : (g.attenuate c).Sub g :=
  ⟨Im.attenuate_sub _ _, Im.attenuate_sub _ _⟩

theorem Grants.sub_trans {a b c : Grants} (h1 : a.Sub b) (h2 : b.Sub c) : a.Sub c :=
  ⟨Perms.sub_trans h1.1 h2.1, Perms.sub_trans h1.2 h2.2⟩

/-- A chain of attenuated grants stays inside the root grants. -/
theorem Grants.attenuateAll_sub (g : Grants) (cs : List Grants) : (g.attenuateAll cs).Sub g := by
  induction cs generalizing g with
  | nil => exact ⟨fun _ h => h, fun _ h => h⟩
  | cons c cs ih =>
    show (Grants.attenuateAll (g.attenuate c) cs).Sub g
    exact Grants.sub_trans (ih (g.attenuate c)) (Grants.attenuate_sub g c)

/-- What a door passes for a smaller grant, it passes for the larger one. -/
theorem Grants.pass_of_sub {g h : Grants} (hs : g.Sub h) (s : Sentence) (hp : decideSentence g s = .pass) :
    decideSentence h s = .pass := by
  obtain ⟨h1, h2⟩ := pass_needs_both_grants g s hp
  unfold decideSentence
  simp [hs.1 _ h1, hs.2 _ h2]

/-- What a door passes for attenuated grants, it passes for the parents. -/
theorem Grants.pass_of_attenuated (g c : Grants) (s : Sentence) (hp : decideSentence (g.attenuate c) s = .pass) :
    decideSentence g s = .pass :=
  Grants.pass_of_sub (Grants.attenuate_sub g c) s hp

/-- Along any chain of attenuations the passing sentences only shrink: whatever passes at the end passed at the root. -/
theorem Grants.pass_of_attenuateAll (g : Grants) (cs : List Grants) (s : Sentence)
    (hp : decideSentence (g.attenuateAll cs) s = .pass) : decideSentence g s = .pass :=
  Grants.pass_of_sub (Grants.attenuateAll_sub g cs) s hp

/-- What the root's door refuses, every attenuation refuses. -/
theorem Grants.refuse_of_attenuateAll (g : Grants) (cs : List Grants) (s : Sentence) (hr : decideSentence g s = .refuse) :
    decideSentence (g.attenuateAll cs) s = .refuse := by
  cases hd : decideSentence (g.attenuateAll cs) s with
  | refuse => rfl
  | pass => rw [Grants.pass_of_attenuateAll g cs s hd] at hr; cases hr

/-- The empty grant attenuates only to itself: nothing attenuates into authority. -/
theorem Grants.attenuate_noGrants (c : Grants) : noGrants.attenuate c = noGrants := by
  unfold Grants.attenuate noGrants
  congr 1 <;> funext k <;> simp [Im.attenuate]

/-- Deciding a sentence yields a verdict, one of two values, and no grant: the door's only output is `pass` or `refuse`, so no
    sentence creates authority. -/
theorem decide_is_verdict (g : Grants) (s : Sentence) :
    decideSentence g s = .pass ∨ decideSentence g s = .refuse := by
  cases decideSentence g s <;> simp

end Im
