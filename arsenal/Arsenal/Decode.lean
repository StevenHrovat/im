/-
Encoding, decoding, and smelly states.
Released under the Apache License 2.0.
-/
import Mathlib
import Arsenal.FullTurn
import Arsenal.Toy

/-!
# Encoding, decoding, and smelly states

An *encoding* is a map `enc : α → β`, a *decoder* a map back `dec : β → α`. A state `x` is **smelly** (the first author's word) when
decoding its encoding does not return it: `dec (enc x) ≠ x`. The rotational symmetry is then not positive: the turn out and back
did not close.

**What is proved.**
* `never_smelly_iff`: a decoder that is never smelly is exactly a left inverse of the encoding.
* `exists_clean_decoder`: an injective encoding has a decoder that is never smelly.
* `smelly_of_not_injective`: a lossy encoding (not injective) makes every decoder smelly somewhere.
* `hash_smelly`: every map from an infinite type to a finite one, every hash, makes every decoder smelly somewhere. A digest is traced
  to an origin consistent with it, never decoded back to the one input.
* `turn_decodes`: the full turn is a decoder that is never smelly on the `N` coefficients it encodes: evaluating them at the powers of
  a primitive `N`-th root of unity and averaging one turn back returns every one (`Arsenal.FullTurn.full_turn_coeff`).
* `toy_smelly_iff`: the toy's smelly states (`Arsenal.Toy.Smelly`, rotating `vxunderground` by `k` and back by `k'`) are this notion,
  with the rotations as encoding and decoder.

Mathlib alone, nothing open.
-/

namespace Arsenal.Decode

open Finset

/-- **Smelly**: decoding the encoding of `x` does not return `x`. -/
def Smelly {α β : Type*} (enc : α → β) (dec : β → α) (x : α) : Prop := dec (enc x) ≠ x

/-- **Never smelly is a left inverse**: a decoder is never smelly exactly when it undoes the encoding everywhere. -/
theorem never_smelly_iff {α β : Type*} (enc : α → β) (dec : β → α) :
    (∀ x, ¬ Smelly enc dec x) ↔ Function.LeftInverse dec enc := by
  simp [Smelly, Function.LeftInverse]

/-- **An injective encoding has a decoder that is never smelly.** -/
theorem exists_clean_decoder {α β : Type*} [Nonempty α] {enc : α → β} (h : Function.Injective enc) :
    ∃ dec : β → α, ∀ x, ¬ Smelly enc dec x :=
  ⟨Function.invFun enc, (never_smelly_iff _ _).2 (Function.leftInverse_invFun h)⟩

/-- **A lossy encoding makes every decoder smelly somewhere.** -/
theorem smelly_of_not_injective {α β : Type*} {enc : α → β} (h : ¬ Function.Injective enc) (dec : β → α) :
    ∃ x, Smelly enc dec x := by
  by_contra hc
  push Not at hc
  exact h ((never_smelly_iff enc dec).1 hc).injective

/-- **Every hash makes every decoder smelly somewhere**: a map from an infinite type (all messages) to a finite one (all digests)
is not injective. -/
theorem hash_smelly {α β : Type*} [Infinite α] [Finite β] (h : α → β) (dec : β → α) : ∃ x, Smelly h dec x := by
  apply smelly_of_not_injective _ dec
  intro hinj
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite h
  exact hab (hinj he)

/-- The full turn as an encoding: the `N` coefficients `c 0, ..., c (N - 1)` read at the powers of `ζ`. -/
def turnEnc {K : Type*} [Field K] (ζ : K) (N : ℕ) (c : ℕ → K) : ℕ → K :=
  fun j => ∑ m ∈ range N, c m * ζ ^ (j * m)

/-- The full turn back as a decoder: the average over one turn, against the inverse powers. -/
def turnDec {K : Type*} [Field K] (ζ : K) (N : ℕ) (v : ℕ → K) : ℕ → K :=
  fun k => (N : K)⁻¹ * ∑ j ∈ range N, v j * ζ ^ (j * (N - k))

/-- **The full turn decodes**: for a primitive `N`-th root of unity, decoding the encoding returns every one of the `N` coefficients,
so the full turn is never smelly on them. -/
theorem turn_decodes {K : Type*} [Field K] [CharZero K] {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (c : ℕ → K)
    {k : ℕ} (hk : k < N) : turnDec ζ N (turnEnc ζ N c) k = c k :=
  Arsenal.FullTurn.full_turn_coeff hζ c hk

/-- **The toy's smelly states are this notion**: rotating `vxunderground` by `k` is the encoding, rotating by `k'` the decoder. -/
theorem toy_smelly_iff (k k' : ℕ) :
    Arsenal.Toy.Smelly k k' ↔ Smelly (List.map (Arsenal.Toy.rot k)) (List.map (Arsenal.Toy.rot k')) Arsenal.Toy.vx :=
  Iff.rfl

end Arsenal.Decode
