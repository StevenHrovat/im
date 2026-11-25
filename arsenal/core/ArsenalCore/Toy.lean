/-
The finite layer of the verify toy, on Lean's kernel alone.
Released under the Apache License 2.0.
-/

/-!
# The verify toy's finite layer, without Mathlib

Nothing is imported, not even Mathlib, and the package has no requirement. The facts about bytes and the string are decided by the
kernel's evaluation; the general facts about words of every length are proved from Lean's core lemmas on natural numbers. What is
trusted is the kernel, with its built-in arithmetic on natural numbers, Lean's prelude definitions and the axioms the report lists.
A definition is the specification here too: `rotl` is a rotation for words below `2 ^ n`, and `Smelly` is about the one string.

Lean need not trust a library: every Mathlib proof is a term that a small kernel can check again (the de Bruijn
criterion). Mathlib's own build does; prebuilt files fetched by `lake exe cache get` are loaded without a new check, and a
replay (Lean's `lean4checker`, or a second kernel such as nanoda over `lean4export`) repeats the check locally. What is trusted
is the kernel, with its built-in arithmetic on natural numbers, Lean's prelude definitions and the axioms the report lists. What the arsenal takes from Mathlib is its definitions (the complex numbers, the circle, the integral), which state
what infinite objects mean; no evaluation can establish those, so the analytic layer (`Arsenal`, one directory up) imports Mathlib as
an API, and this layer does not need to.

**The string** `vxunderground` (`vx`), its bytes. **Smelly**: rotating the letters by `k` and then `k'` does not return the string,
exactly when `k + k'` is not a multiple of 26 (`smelly_iff_not_full`). **Moin, the leading zero**: rotating an `n`-bit word left is an
exact doubling exactly when its leading bit is 0 (`rotl_eq_double_iff`), decided on every byte (`moin_byte`); every byte of the
string has one (`vx_rotl`). **Moin is not the opposite of smelly**: a bit rotation is never smelly, since rotating back returns every
byte, leading one or not (`rotl_never_smelly`). A rotation never loses a bit; Moin asks whether it acted as a doubling (no bit
wrapped round), smelly whether the round trip came back.
-/

namespace ArsenalCore.Toy

/-! ## The string -/

/-- **`vxunderground` as bytes**. -/
def vx : List Nat := [118, 120, 117, 110, 100, 101, 114, 103, 114, 111, 117, 110, 100]

/-- **The conversion**: the bytes are exactly the characters of the string. -/
theorem vx_eq : "vxunderground".toList.map Char.toNat = vx := by decide

/-- **Every byte is a lowercase letter**. -/
theorem vx_lower : ∀ b ∈ vx, 97 ≤ b ∧ b ≤ 122 := by decide

/-! ## Rotating the letters: the full turn, and smelly -/

/-- **Rotation of the 26 letters by `k`** (other bytes unchanged). -/
def rot (k b : Nat) : Nat := if 97 ≤ b ∧ b ≤ 122 then 97 + (b - 97 + k) % 26 else b

/-- **The half-turn hides the string**. -/
theorem vx_rot13 : vx.map (rot 13) = "ikhaqretebhaq".toList.map Char.toNat := by decide

/-- **The full turn returns it**: 13 + 13 = 26. -/
theorem vx_rot13_twice : (vx.map (rot 13)).map (rot 13) = vx := by decide

/-- **Smelly**: rotating by `k` and then by `k'` does not return the string. -/
def Smelly (k k' : Nat) : Prop := (vx.map (rot k)).map (rot k') ≠ vx

instance (k k' : Nat) : Decidable (Smelly k k') := by
  unfold Smelly
  infer_instance

/-- **Smelly exactly when the turn is not full** (all 676 pairs below 26, one kernel evaluation). -/
theorem smelly_iff_not_full : ∀ k < 26, ∀ k' < 26, (Smelly k k' ↔ (k + k') % 26 ≠ 0) := by decide +kernel

/-- **Rotations add** (all 676 pairs). -/
theorem rot_add : ∀ a < 26, ∀ b < 26, (vx.map (rot a)).map (rot b) = vx.map (rot ((a + b) % 26)) := by decide +kernel

/-! ## Rotating the bits: Moin, the leading zero -/

/-- **Rotating an `n`-bit word left by one place**: the leading bit comes round to the end. -/
def rotl (n x : Nat) : Nat := (2 * x) % 2 ^ n + x / 2 ^ (n - 1)

/-- **Rotating an `n`-bit word right by one place**: the last bit comes round to the top. -/
def rotr (n x : Nat) : Nat := x / 2 + (x % 2) * 2 ^ (n - 1)

theorem two_pow_pred {n : Nat} (hn : 1 ≤ n) : 2 ^ n = 2 * 2 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.pow_succ']

/-- **A leading zero is rotated away**: the rotation is an exact doubling. -/
theorem rotl_of_leading_zero {n x : Nat} (hn : 1 ≤ n) (hx : x < 2 ^ (n - 1)) : rotl n x = 2 * x := by
  unfold rotl
  rw [two_pow_pred hn]
  generalize 2 ^ (n - 1) = q at *
  rw [Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt hx, Nat.add_zero]

/-- **A leading one comes round**: `rotl n x + 2 ^ n = 2 * x + 1`. -/
theorem rotl_of_leading_one {n x : Nat} (hn : 1 ≤ n) (h1 : 2 ^ (n - 1) ≤ x) (h2 : x < 2 ^ n) :
    rotl n x + 2 ^ n = 2 * x + 1 := by
  have hq : 0 < 2 ^ (n - 1) := Nat.two_pow_pos (n - 1)
  unfold rotl
  rw [two_pow_pred hn] at h2 ⊢
  generalize 2 ^ (n - 1) = q at *
  have hd : x / q = 1 := by
    apply Nat.le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hq).2 (by omega))
    · exact (Nat.le_div_iff_mul_le hq).2 (by omega)
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), hd]
  omega

/-- **The certificate**: rotating left is an exact doubling exactly when the leading bit is 0. -/
theorem rotl_eq_double_iff {n x : Nat} (hn : 1 ≤ n) (h2 : x < 2 ^ n) : rotl n x = 2 * x ↔ x < 2 ^ (n - 1) := by
  refine ⟨fun h => ?_, rotl_of_leading_zero hn⟩
  have hq : 0 < 2 ^ (n - 1) := Nat.two_pow_pos (n - 1)
  by_cases h1 : x < 2 ^ (n - 1)
  · exact h1
  · have h3 := rotl_of_leading_one hn (Nat.not_lt.mp h1) h2
    omega

/-- **Moin, decided on every byte**: all 256 bytes, one kernel evaluation. -/
theorem moin_byte : ∀ b < 256, (rotl 8 b = 2 * b ↔ b < 128) := by decide +kernel

/-- **A bit rotation is never smelly**: rotating back returns every byte, leading one or not. -/
theorem rotl_never_smelly : ∀ b < 256, rotr 8 (rotl 8 b) = b := by decide +kernel

/-- **Every byte of the string has a leading zero**. -/
theorem vx_leading_zero : ∀ b ∈ vx, b < 2 ^ 7 := by decide

/-- **Rotating every byte of the string doubles it exactly**. -/
theorem vx_rotl : vx.map (rotl 8) = vx.map (2 * ·) := by decide

end ArsenalCore.Toy
