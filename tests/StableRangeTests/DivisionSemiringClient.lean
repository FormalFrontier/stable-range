/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import StableRange
public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Real.Basic
import Mathlib.Basic.NNReal.Defs
import Mathlib.Tactic.NormNum

/-!
# Division-semiring local-ring clients

These examples use the ordinary library root for locality of division semirings,
the additive submonoid of nonunits, and the additive view of the maximal ideal.
Over fields, the unit criteria use the existing local-ring projections, and the
additive comparison consumes Mathlib's existing maximal-ideal equality.

The nonnegative reals provide a commutative semifield with a pair of halves
summing to one, while no nonnegative real is an additive inverse of one.
The real quaternions provide a division ring with noncommuting generators.
The arithmetic and noncommutativity witnesses do not use the locality or
nonunit-submonoid conclusions.

## References

* Mathlib, `RingTheory.LocalRing.Basic` (the field-locality instance and unit
  criteria), `RingTheory.LocalRing.MaximalIdeal.Basic` (the existing maximal
  ideal and its equality with the zero ideal over fields), and
  `Algebra.Module.Submodule.Lattice` (the additive view of the zero submodule).
* Mathlib, `Basic.NNReal.Defs` and `Algebra.Quaternion` (the canonical semifield
  of nonnegative reals and the real quaternion division ring).
* `StableRange.Local`, for division-semiring locality and the additive views
  of nonunits and maximal ideals.
-/

set_option warningAsError true

@[expose] public section

namespace StableRangeTests.DivisionSemiringClient

open scoped NNReal Quaternion

universe u

example (K : Type u) [DivisionSemiring K] : IsLocalRing K :=
  DivisionSemiring.isLocalRing K

private theorem fieldUnitSummand (K : Type u) [Field K] (a b : K) (h : a + b = 1) :
    IsUnit a ∨ IsUnit b := by
  let : IsLocalRing K := DivisionSemiring.isLocalRing K
  exact IsLocalRing.isUnit_or_isUnit_of_add_one h

private theorem fieldUnitComplement (K : Type u) [Field K] (a : K) :
    IsUnit a ∨ IsUnit (1 - a) := by
  let : IsLocalRing K := DivisionSemiring.isLocalRing K
  exact IsLocalRing.isUnit_or_isUnit_one_sub_self a

private theorem semifieldMaximalIdealAdditive (K : Type u) [Semifield K] :
    (IsLocalRing.maximalIdeal K).toAddSubmonoid = ⊥ := by
  let : IsLocalRing K := DivisionSemiring.isLocalRing K
  rw [IsLocalRing.maximalIdeal_toAddSubmonoid]
  exact IsLocalRing.nonunitsAddSubmonoid_eq_bot K

private theorem fieldNonunitsAdditive (K : Type u) [Field K] :
    IsLocalRing.nonunitsAddSubmonoid K = ⊥ := by
  let : IsLocalRing K := DivisionSemiring.isLocalRing K
  rw [← IsLocalRing.maximalIdeal_toAddSubmonoid, IsLocalRing.maximalIdeal_eq_bot]
  exact Submodule.bot_toAddSubmonoid

example (a b : ℚ) (h : a + b = 1) : IsUnit a ∨ IsUnit b :=
  fieldUnitSummand ℚ a b h

example (a : ℚ) : IsUnit a ∨ IsUnit (1 - a) :=
  fieldUnitComplement ℚ a

example : IsLocalRing.nonunitsAddSubmonoid ℚ = ⊥ :=
  fieldNonunitsAdditive ℚ

example (K : Type u) [DivisionSemiring K] (a : K) :
    a ∈ IsLocalRing.nonunitsAddSubmonoid K ↔ a = 0 := by
  let : IsLocalRing K := DivisionSemiring.isLocalRing K
  simp only [IsLocalRing.nonunitsAddSubmonoid_eq_bot, AddSubmonoid.mem_bot]

noncomputable example : Semifield ℝ≥0 := inferInstance

example : IsLocalRing ℝ≥0 := DivisionSemiring.isLocalRing ℝ≥0

private noncomputable def nnrealHalf : ℝ≥0 :=
  NNReal.mk (1 / 2) (by norm_num)

private theorem nnrealHalf_add_self : nnrealHalf + nnrealHalf = 1 := by
  apply NNReal.coe_injective
  norm_num [nnrealHalf]

private theorem nnreal_one_add_ne_zero : ∀ b : ℝ≥0, 1 + b ≠ 0 := by
  intro b h
  have hreal : (1 : ℝ) + (b : ℝ) = 0 := by
    simpa only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_zero] using
      congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) h
  have hpositive : (0 : ℝ) < 1 + (b : ℝ) :=
    add_pos_of_pos_of_nonneg zero_lt_one (NNReal.coe_nonneg b)
  exact (ne_of_gt hpositive) hreal

example : nnrealHalf + nnrealHalf = 1 ∧ ∀ b : ℝ≥0, 1 + b ≠ 0 :=
  ⟨nnrealHalf_add_self, nnreal_one_add_ne_zero⟩

example : IsUnit nnrealHalf ∨ IsUnit nnrealHalf := by
  let : IsLocalRing ℝ≥0 := DivisionSemiring.isLocalRing ℝ≥0
  exact IsLocalRing.isUnit_or_isUnit_of_add_one nnrealHalf_add_self

example : (IsLocalRing.maximalIdeal ℝ≥0).toAddSubmonoid = ⊥ :=
  semifieldMaximalIdealAdditive ℝ≥0

private def quaternionI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩

private def quaternionJ : ℍ[ℝ] := ⟨0, 0, 1, 0⟩

private theorem quaternion_noncommuting :
    quaternionI * quaternionJ ≠ quaternionJ * quaternionI := by
  intro h
  have hk := congrArg QuaternionAlgebra.imK h
  norm_num [quaternionI, quaternionJ, Quaternion.imK_mul] at hk

noncomputable example : DivisionRing ℍ[ℝ] := inferInstance

example : IsLocalRing ℍ[ℝ] := DivisionSemiring.isLocalRing ℍ[ℝ]

/-- The real quaternions contain noncommuting elements, namely the generators
`i` and `j`. -/
public theorem quaternion_noncommutative : ∃ x y : ℍ[ℝ], x * y ≠ y * x :=
  ⟨quaternionI, quaternionJ, quaternion_noncommuting⟩

example (q : ℍ[ℝ]) : q ∈ IsLocalRing.nonunitsAddSubmonoid ℍ[ℝ] ↔ q = 0 := by
  let : IsLocalRing ℍ[ℝ] := DivisionSemiring.isLocalRing ℍ[ℝ]
  simp only [IsLocalRing.nonunitsAddSubmonoid_eq_bot, AddSubmonoid.mem_bot]

end StableRangeTests.DivisionSemiringClient
