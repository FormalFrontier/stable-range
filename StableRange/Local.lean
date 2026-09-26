/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import StableRange.Basic
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Stable range of local rings

This file proves that every noncommutative local ring in mathlib's sense has
Bass stable range one.
-/

set_option warningAsError true

@[expose] public section

open scoped BigOperators

namespace Bass

universe u

variable {R : Type u} [Ring R]

/-- In a noncommutative local ring, an element with a right inverse is a unit.

The proof does not assume direct finiteness. It applies locality to the
idempotent `b * a`; if `1 - b * a` were a unit, then its product with `b`
would force `b = 0`, contradicting `a * b = 1`. -/
theorem isUnit_of_mul_eq_one_right [IsLocalRing R]
    {a b : R} (hab : a * b = 1) : IsUnit a := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (b * a) with hba | hba
  · let c : R := (↑(hba.unit⁻¹) : R) * b
    have hca : c * a = 1 := by
      calc
        c * a = (↑(hba.unit⁻¹) : R) * (b * a) := by
          simp only [c, mul_assoc]
        _ = (↑(hba.unit⁻¹) : R) * (hba.unit : R) := by
          exact congrArg (fun x : R ↦ (↑(hba.unit⁻¹) : R) * x)
            hba.unit_spec.symm
        _ = 1 := Units.inv_mul hba.unit
    have hcb : c = b := by
      calc
        c = c * 1 := by rw [mul_one]
        _ = c * (a * b) := by rw [hab]
        _ = (c * a) * b := (mul_assoc c a b).symm
        _ = b := by rw [hca, one_mul]
    exact ⟨⟨a, b, hab, hcb ▸ hca⟩, rfl⟩
  · have hzero : (1 - b * a) * b = 0 := by
      simp only [sub_mul, one_mul, mul_assoc, hab, mul_one, sub_self]
    have hb0 : b = 0 := hba.mul_right_eq_zero.mp hzero
    rw [hb0, mul_zero] at hab
    exact (zero_ne_one hab).elim

/-- In a local ring, one entry of a right-unimodular pair is a unit. -/
theorem isUnit_first_or_isUnit_second [IsLocalRing R]
    (r0 : R) (r : Fin 1 → R) (hr : IsRightUnimodularCons r0 r) :
    IsUnit r0 ∨ IsUnit (r 0) := by
  obtain ⟨s0, s, hs⟩ := hr
  have hsum : IsUnit (r0 * s0 + r 0 * s 0) := by
    have : r0 * s0 + r 0 * s 0 = 1 := by
      simpa only [Fin.sum_univ_one] using hs
    rw [this]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with h0 | h1
  · obtain ⟨u, hu⟩ := h0
    apply Or.inl
    apply isUnit_of_mul_eq_one_right (b := s0 * (↑(u⁻¹) : R))
    calc
      r0 * (s0 * (↑(u⁻¹) : R)) =
          (r0 * s0) * (↑(u⁻¹) : R) := by rw [mul_assoc]
      _ = (u : R) * (↑(u⁻¹) : R) := by rw [← hu]
      _ = 1 := Units.val_inv u
  · obtain ⟨u, hu⟩ := h1
    apply Or.inr
    apply isUnit_of_mul_eq_one_right (b := s 0 * (↑(u⁻¹) : R))
    calc
      r 0 * (s 0 * (↑(u⁻¹) : R)) =
          (r 0 * s 0) * (↑(u⁻¹) : R) := by rw [mul_assoc]
      _ = (u : R) * (↑(u⁻¹) : R) := by rw [← hu]
      _ = 1 := Units.val_inv u

/-- Every local ring satisfies Bass's condition `(S_1)`. -/
theorem stableRangeCondition_one_of_isLocalRing [IsLocalRing R] :
    StableRangeCondition R 1 := by
  intro r0 r hr
  rcases isUnit_first_or_isUnit_second r0 r hr with h0 | h1
  · let a : Rˣ := h0.unit
    refine ⟨fun _ ↦ (↑(a⁻¹) : R) * (r 0 - 1), ?_⟩
    refine ⟨fun _ ↦ 1, ?_⟩
    rw [Fin.sum_univ_one]
    simp only [mul_one]
    have hInv : r0 * (↑(a⁻¹) : R) = 1 := by
      rw [← h0.unit_spec]
      exact Units.val_inv a
    rw [← mul_assoc, hInv, one_mul, sub_sub_cancel]
  · let a : Rˣ := h1.unit
    refine ⟨fun _ ↦ 0, ?_⟩
    refine ⟨fun _ ↦ (↑(a⁻¹) : R), ?_⟩
    rw [Fin.sum_univ_one]
    simp only [mul_zero, sub_zero]
    rw [← h1.unit_spec]
    exact Units.val_inv a

/-- In a nontrivial ring, Bass's condition `(S_0)` is impossible. -/
theorem not_stableRangeCondition_zero [Nontrivial R] :
    ¬ StableRangeCondition R 0 := by
  intro h
  let empty : Fin 0 → R := fun i ↦ Fin.elim0 i
  have hCons : IsRightUnimodularCons (1 : R) empty := by
    refine ⟨1, empty, ?_⟩
    simp [empty]
  obtain ⟨_, w, hw⟩ := h 1 empty hCons
  have h01 : (0 : R) = 1 := by
    simpa only [Finset.univ_eq_empty, Finset.sum_empty] using hw
  exact zero_ne_one h01

/-- Every local ring has least Bass stable range one. -/
theorem stableRange_one_of_isLocalRing [IsLocalRing R] :
    IsStableRange R 1 := by
  refine ⟨stableRangeCondition_one_of_isLocalRing, ?_⟩
  intro n hn
  cases n with
  | zero => exact (not_stableRangeCondition_zero hn).elim
  | succ n => exact Nat.succ_le_succ (Nat.zero_le n)

end Bass
