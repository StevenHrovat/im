/-
The verify toy: binary.
Released under the Apache License 2.0.
-/
import Mathlib
import Arsenal.R136a1
import Arsenal.Rotation
import Arsenal.Observable

/-!
# The verify toy: binary

A small, complete example of the observable API (`Arsenal.Observable`), on binary words, to read and to rerun.

**A box that passes, at every scale.** `evens k`: the `k`-bit words, stepping by two modulo `2 ^ k`, with the claim "even". The
route is shown (`evens_route`): `0` is even and a step of two keeps a word even. On a byte the step is also checked by one kernel
evaluation over all 256 states (`evens_step_byte`). Every bit width shares the gate with one bit, by reduction modulo 2
(`toBit`, `evens_shared`), so here the sharing across scales is **proved**, not assumed, and the route at one bit certifies every
bit width (`evens_everywhere`).

**A box that says R136a1.** `counter k`: the same words stepping by one, a binary counter, with the same claim. At tick 1 the word is
`1`: the gate reads `r136a1` while the marker claims `inside` (`counter_gate`), so the box is refuted (`counter_refuted`).

**Reassembly.** Two routes shown separately give a route for the pair (`pair_route`, from `Observable.route_prod`): a bigger proof is
the parts reassembled as the API guides.

Mathlib alone, nothing open.
-/

noncomputable section

namespace Arsenal.Toy

open Arsenal Arsenal.Rotation

/-- The `k`-bit word one step on, by `d`, modulo `2 ^ k`. -/
def bump (k d : ℕ) (x : Fin (2 ^ k)) : Fin (2 ^ k) := ⟨(x.val + d) % 2 ^ k, Nat.mod_lt _ (by positivity)⟩

/-- The zero word. -/
def zero (k : ℕ) : Fin (2 ^ k) := ⟨0, by positivity⟩

/-- **`k`-bit words stepping by two**, with the claim "even". -/
def evens (k : ℕ) : Observable := ⟨Fin (2 ^ k), bump k 2, fun x => 2 ∣ x.val, fun _ => inferInstance⟩

/-- **`k`-bit words stepping by one** (a binary counter), with the claim "even". -/
def counter (k : ℕ) : Observable := ⟨Fin (2 ^ k), bump k 1, fun x => 2 ∣ x.val, fun _ => inferInstance⟩

/-! ## A box that passes -/

/-- A step of two keeps a word even. -/
theorem evens_step (k : ℕ) (x : Fin (2 ^ k)) (hx : 2 ∣ x.val) : 2 ∣ (bump k 2 x).val := by
  show 2 ∣ (x.val + 2) % 2 ^ k
  rcases k with _ | k
  · simp
  · rw [Nat.dvd_mod_iff (dvd_pow_self 2 (Nat.succ_ne_zero k))]
    exact dvd_add hx (dvd_refl 2)

/-- **The route, shown**: every word reached from `0` by steps of two is even, at every tick. -/
theorem evens_route (k : ℕ) : (evens k).box.DMPComplete (zero k) :=
  (evens k).route (show 2 ∣ 0 from dvd_zero 2) (fun x hx => evens_step k x hx)

/-- **The step on a byte, checked by one kernel evaluation** over all 256 states. -/
theorem evens_step_byte : ∀ x : Fin (2 ^ 8), 2 ∣ x.val → 2 ∣ (bump 8 2 x).val := by decide +kernel

/-! ## Every bit width shares the gate with one bit -/

/-- **Reduction modulo 2**: a reconstruction of the `k`-bit box from the one-bit box, keeping the step and the gate factor. -/
def toBit (k : ℕ) (hk : 1 ≤ k) : Box.Hom (evens k).box (evens 1).box where
  toFun x := ⟨x.val % 2, by rw [pow_one]; exact Nat.mod_lt _ (by norm_num)⟩
  step_comm y := by
    apply Fin.ext
    show (y.val + 2) % 2 ^ k % 2 = (y.val % 2 + 2) % 2 ^ 1
    rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega : k ≠ 0)), pow_one]
    omega
  fac_eq y := by
    have h : 2 ∣ y.val % 2 ↔ 2 ∣ y.val := Nat.dvd_mod_iff (dvd_refl 2)
    show (if 2 ∣ y.val % 2 then (0 : ℝ) else 1) = if 2 ∣ y.val then 0 else 1
    by_cases hy : 2 ∣ y.val <;> simp [hy, h]

/-- **The sharing, proved**: every bit width `k ≥ 1` is rebuilt from one bit through its gate, start to start. -/
theorem evens_shared :
    Box.SharedGate (evens 1).box (zero 1) (fun k : {k : ℕ // 1 ≤ k} => (evens k.1).box) (fun k => zero k.1) :=
  fun k => ⟨rfl, toBit k.1 k.2, Fin.ext (Nat.zero_mod 2), fun _ => rfl⟩

/-- **Certified universally, the sharing proved**: the route at one bit certifies every bit width. -/
theorem evens_everywhere : ∀ k : {k : ℕ // 1 ≤ k}, (evens k.1).box.DMPComplete (zero k.1) :=
  (evens 1).route_everywhere (x₀ := zero 1) (show 2 ∣ 0 from dvd_zero 2) (fun x hx => evens_step 1 x hx)
    (fun k : {k : ℕ // 1 ≤ k} => (evens k.1).box) (fun k => zero k.1) evens_shared

/-! ## A box that says R136a1 -/

/-- At tick 1 the counter shows the word `1`. -/
theorem counter_tick_one (k : ℕ) (hk : 1 ≤ k) : ((counter k).step^[1] (zero k)).val = 1 := by
  show (0 + 1) % 2 ^ k = 1
  exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))

/-- **The gate says R136a1 at tick 1**: the word `1` is odd, so the gate reads outside. -/
theorem counter_gate (k : ℕ) (hk : 1 ≤ k) :
    (counter k).box.gate ((counter k).step^[1] (zero k)) = .r136a1 := by
  refine (Box.gate_eq_r136a1_iff _ _).2 ?_
  show (0 : ℝ) < if 2 ∣ ((counter k).step^[1] (zero k)).val then 0 else 1
  rw [counter_tick_one k hk]
  norm_num

/-- **Refuted**: the marker claims inside at tick 1, where the gate says R136a1. -/
theorem counter_refuted (k : ℕ) (hk : 1 ≤ k) : ¬ (counter k).box.DMPComplete (zero k) :=
  (counter k).refuted_by_tick 1 (fun h => by
    have h' : 2 ∣ ((counter k).step^[1] (zero k)).val := h
    rw [counter_tick_one k hk] at h'
    norm_num at h')

/-- **On a byte, by one kernel evaluation**: the counter's first word is odd. -/
theorem counter_byte : ¬ 2 ∣ (bump 8 1 (zero 8)).val := by decide +kernel

/-! ## Reassembly -/

/-- **Reassembled by the API**: a byte and a 16-bit word, each stepping by two, run side by side, have a route. -/
theorem pair_route : ((evens 8).prod (evens 16)).box.DMPComplete (zero 8, zero 16) :=
  Observable.route_prod (evens_route 8) (evens_route 16)

end Arsenal.Toy
