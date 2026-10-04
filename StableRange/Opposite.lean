/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Regular
import Mathlib.Algebra.Group.Units.Opposite
import Mathlib.Tactic.NoncommRing

/-!
# Stable range one and opposite rings

The index-one stable-range condition is expressed on right-unimodular rows.
The opposite-ring formulation reverses the order of multiplication in these
rows.
-/

set_option warningAsError true

@[expose] public section

namespace Bass

universe u

variable {R : Type u} [Ring R]

private theorem isUnit_add_sub_mul_swap (a b x : R)
    (h : IsUnit (a + b - a * x * b)) : IsUnit (a + b - b * x * a) := by
  obtain ⟨inverse, hmul, hmul'⟩ := isUnit_iff_exists.mp h
  have hleft : (a + b - b * x * a) * (1 - x * b) =
      (1 - b * x) * (a + b - a * x * b) := by noncomm_ring
  have hright : (1 - a * x) * (a + b - b * x * a) =
      (a + b - a * x * b) * (1 - x * a) := by noncomm_ring
  refine isUnit_iff_exists.mpr ⟨x + (1 - x * b) * inverse * (1 - a * x), ?_, ?_⟩
  · calc
      (a + b - b * x * a) * (x + (1 - x * b) * inverse * (1 - a * x)) =
          (a + b - b * x * a) * x +
            ((a + b - b * x * a) * (1 - x * b)) * inverse * (1 - a * x) := by
              noncomm_ring
      _ = (a + b - b * x * a) * x +
            ((1 - b * x) * (a + b - a * x * b)) * inverse * (1 - a * x) := by
              rw [hleft]
      _ = (a + b - b * x * a) * x +
            (1 - b * x) * ((a + b - a * x * b) * inverse) * (1 - a * x) := by
              noncomm_ring
      _ = (a + b - b * x * a) * x +
            (1 - b * x) * (1 - a * x) := by
        rw [hmul]
        simp
      _ = 1 := by noncomm_ring
  · calc
      (x + (1 - x * b) * inverse * (1 - a * x)) * (a + b - b * x * a) =
          x * (a + b - b * x * a) + (1 - x * b) * inverse *
            ((1 - a * x) * (a + b - b * x * a)) := by noncomm_ring
      _ = x * (a + b - b * x * a) + (1 - x * b) * inverse *
            ((a + b - a * x * b) * (1 - x * a)) := by rw [hright]
      _ = x * (a + b - b * x * a) +
            (1 - x * b) * (inverse * (a + b - a * x * b)) * (1 - x * a) := by
              noncomm_ring
      _ = x * (a + b - b * x * a) + (1 - x * b) * (1 - x * a) := by
        rw [hmul']
        simp
      _ = 1 := by noncomm_ring

private theorem stableRangeCondition_one_iff_forall_isUnit_add_sub_mul :
    StableRangeCondition R 1 ↔
      ∀ a x : R, ∃ b : R, IsUnit (a + b - a * x * b) := by
  constructor
  · intro h a x
    obtain ⟨t, ht⟩ :=
      (stableRangeCondition_one_iff_forall_isUnit_sub_mul.mp h) (1 - a * x) a
        ⟨1, x, by noncomm_ring⟩
    refine ⟨-t, ?_⟩
    convert ht using 1
    noncomm_ring
  · intro h
    apply stableRangeCondition_one_iff_forall_isUnit_sub_mul.mpr
    intro a b hpair
    obtain ⟨s, w, hrow⟩ := hpair
    obtain ⟨t, ht⟩ := h b w
    refine ⟨-s * t, ?_⟩
    have hs : a * s = 1 - b * w := by
      calc
        a * s = (a * s + b * w) - b * w := by noncomm_ring
        _ = 1 - b * w := by rw [hrow]
    have heq : b - a * (-s * t) = b + t - b * w * t := by
      calc
        b - a * (-s * t) = b + (a * s) * t := by noncomm_ring
        _ = b + (1 - b * w) * t := by rw [hs]
        _ = b + t - b * w * t := by noncomm_ring
    rw [heq]
    exact ht

/-- Bass's stable-range-one condition passes to the opposite ring. -/
theorem stableRangeCondition_one_opposite
    (h : StableRangeCondition R 1) : StableRangeCondition Rᵐᵒᵖ 1 := by
  apply stableRangeCondition_one_iff_forall_isUnit_add_sub_mul.mpr
  intro a x
  obtain ⟨b, hb⟩ :=
    (stableRangeCondition_one_iff_forall_isUnit_add_sub_mul.mp h) a.unop x.unop
  refine ⟨MulOpposite.op b, ?_⟩
  have hswitched : IsUnit (a.unop + b - b * x.unop * a.unop) :=
    isUnit_add_sub_mul_swap a.unop b x.unop hb
  simpa only [MulOpposite.op_add, MulOpposite.op_sub, MulOpposite.op_mul,
    MulOpposite.op_unop, mul_assoc] using hswitched.op

/-- Bass's stable-range-one condition is invariant under passage to the opposite ring. -/
theorem stableRangeCondition_one_opposite_iff :
    StableRangeCondition R 1 ↔ StableRangeCondition Rᵐᵒᵖ 1 := by
  constructor
  · exact stableRangeCondition_one_opposite
  · intro h
    have h' : StableRangeCondition Rᵐᵒᵖᵐᵒᵖ 1 := stableRangeCondition_one_opposite h
    exact h'.map_equiv (RingEquiv.opOp R).symm

end Bass
