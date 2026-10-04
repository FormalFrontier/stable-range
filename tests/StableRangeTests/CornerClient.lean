/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange
public import StableRangeTests.CornerMatrixFixtures
import StableRangeTests.PublicAPIClient
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Idempotent-corner stable-range clients

Three-by-three matrices over a finite nonreduced ring and an infinite product
have noncentral corners containing noncommuting right-unimodular nonunits.
The corner-unit correction is distinguished from an ambient matrix unit.
-/

set_option warningAsError true

@[expose] public section

namespace StableRangeTests.CornerClient

universe u

open StableRangeTests.CornerMatrixFixtures

private theorem zmodFour_condition : Bass.StableRangeCondition (ZMod 4) 1 :=
  Bass.stableRangeCondition_one_of_krullDimLE_zero

private theorem infiniteProduct_condition : Bass.StableRangeCondition (ℕ → ZMod 4) 1 :=
  Bass.stableRangeCondition_pi (fun _ : ℕ => zmodFour_condition)

private theorem zeroRing_condition : Bass.StableRangeCondition (ZMod 1) 1 :=
  Bass.stableRangeCondition_mono (Nat.zero_le 1)
    StableRangePublicAPIClient.zero_ring_condition

private theorem pair_correctable (A : Type u) [Ring A]
    (h : Bass.StableRangeCondition (MatrixRing A) 1) :
    ∃ correction : (e_idempotent A).Corner, IsUnit (bc A - pc A * correction) :=
  (Bass.stableRangeCondition_one_iff_forall_isUnit_sub_mul.mp
    (Bass.stableRangeCondition_one_corner (e_idempotent A) h))
    (pc A) (bc A) ⟨pc A - nc A, rc A, pair_right_witness A⟩

private theorem noncentral_pair_correctable (A : Type u) [Ring A] [Nontrivial A]
    (h : Bass.StableRangeCondition (MatrixRing A) 1) :
    e A * offCorner A = offCorner A ∧ offCorner A * e A = 0 ∧
      offCorner A ≠ 0 ∧ pc A * bc A = nc A ∧ nc A ≠ 0 ∧
      bc A * pc A = 0 ∧ pc A * bc A ≠ bc A * pc A ∧
      ¬ IsUnit (pc A) ∧ ¬ IsUnit (bc A) ∧
      pc A * (pc A - nc A) + bc A * rc A = 1 ∧
      (∃ correction : (e_idempotent A).Corner,
        IsUnit (bc A - pc A * correction)) ∧
      IsUnit (bc A - pc A * (-1)) ∧
      ¬ IsUnit (cornerVal A (bc A - pc A * (-1))) := by
  exact ⟨e_mul_offCorner A, offCorner_mul_e A, offCorner_ne_zero A,
    pc_mul_bc A, nc_ne_zero A, bc_mul_pc A,
    pair_noncommuting A, pc_nonunit A, bc_nonunit A,
    pair_right_witness A, pair_correctable A h,
    explicit_corner_correction A, explicit_ambient_nonunit A⟩

/-- A noncentral corner over `ZMod 4` has a correctable noncommuting pair of nonunits. -/
theorem zmodFour_noncommuting_pair_correctable :
    e (ZMod 4) * offCorner (ZMod 4) = offCorner (ZMod 4) ∧
      offCorner (ZMod 4) * e (ZMod 4) = 0 ∧
      offCorner (ZMod 4) ≠ 0 ∧
      pc (ZMod 4) * bc (ZMod 4) = nc (ZMod 4) ∧ nc (ZMod 4) ≠ 0 ∧
      bc (ZMod 4) * pc (ZMod 4) = 0 ∧
      pc (ZMod 4) * bc (ZMod 4) ≠ bc (ZMod 4) * pc (ZMod 4) ∧
      ¬ IsUnit (pc (ZMod 4)) ∧ ¬ IsUnit (bc (ZMod 4)) ∧
      pc (ZMod 4) * (pc (ZMod 4) - nc (ZMod 4)) + bc (ZMod 4) * rc (ZMod 4) = 1 ∧
      (∃ correction : (e_idempotent (ZMod 4)).Corner,
        IsUnit (bc (ZMod 4) - pc (ZMod 4) * correction)) ∧
      IsUnit (bc (ZMod 4) - pc (ZMod 4) * (-1)) ∧
      ¬ IsUnit (cornerVal (ZMod 4) (bc (ZMod 4) - pc (ZMod 4) * (-1))) := by
  have hNontrivial : Nontrivial (ZMod 4) := ⟨⟨0, 1, by decide⟩⟩
  exact @noncentral_pair_correctable (ZMod 4) _ hNontrivial
    (Bass.stableRangeCondition_one_matrix zmodFour_condition)

example :
    e (ℕ → ZMod 4) * offCorner (ℕ → ZMod 4) = offCorner (ℕ → ZMod 4) ∧
      offCorner (ℕ → ZMod 4) * e (ℕ → ZMod 4) = 0 ∧
      offCorner (ℕ → ZMod 4) ≠ 0 ∧
      pc (ℕ → ZMod 4) * bc (ℕ → ZMod 4) = nc (ℕ → ZMod 4) ∧
      nc (ℕ → ZMod 4) ≠ 0 ∧ bc (ℕ → ZMod 4) * pc (ℕ → ZMod 4) = 0 ∧
      pc (ℕ → ZMod 4) * bc (ℕ → ZMod 4) ≠ bc (ℕ → ZMod 4) * pc (ℕ → ZMod 4) ∧
      ¬ IsUnit (pc (ℕ → ZMod 4)) ∧ ¬ IsUnit (bc (ℕ → ZMod 4)) ∧
      pc (ℕ → ZMod 4) * (pc (ℕ → ZMod 4) - nc (ℕ → ZMod 4)) +
        bc (ℕ → ZMod 4) * rc (ℕ → ZMod 4) = 1 ∧
      (∃ correction : (e_idempotent (ℕ → ZMod 4)).Corner,
        IsUnit (bc (ℕ → ZMod 4) - pc (ℕ → ZMod 4) * correction)) ∧
      IsUnit (bc (ℕ → ZMod 4) - pc (ℕ → ZMod 4) * (-1)) ∧
      ¬ IsUnit (cornerVal (ℕ → ZMod 4)
        (bc (ℕ → ZMod 4) - pc (ℕ → ZMod 4) * (-1))) := by
  have hNontrivial : Nontrivial (ℕ → ZMod 4) := ⟨⟨0, 1, by
    intro h
    exact (show (0 : ZMod 4) ≠ 1 from by decide) (congrFun h 0)⟩⟩
  exact @noncentral_pair_correctable (ℕ → ZMod 4) _ hNontrivial
    (Bass.stableRangeCondition_one_matrix infiniteProduct_condition)

example : ∃ he : IsIdempotentElem (0 : ZMod 4),
    Bass.StableRangeCondition he.Corner 1 ∧ (0 : he.Corner) = 1 := by
  let he : IsIdempotentElem (0 : ZMod 4) := by simp [IsIdempotentElem]
  refine ⟨he, Bass.stableRangeCondition_one_corner he zmodFour_condition, ?_⟩
  apply Subtype.ext
  rfl

example : ∃ he : IsIdempotentElem (1 : ZMod 4),
    Bass.StableRangeCondition he.Corner 1 ∧ (1 : he.Corner) ≠ 0 := by
  let he : IsIdempotentElem (1 : ZMod 4) := by simp [IsIdempotentElem]
  refine ⟨he, Bass.stableRangeCondition_one_corner he zmodFour_condition, ?_⟩
  intro hone
  have hval := congrArg (fun value : he.Corner =>
    ((show Subsemigroup.corner (1 : ZMod 4) from value) : ZMod 4)) hone
  change (1 : ZMod 4) = 0 at hval
  exact (show (1 : ZMod 4) ≠ 0 from by decide) hval

example : ∃ he : IsIdempotentElem (1 : ZMod 1),
    Bass.StableRangeCondition he.Corner 1 ∧ (0 : he.Corner) = 1 := by
  let he : IsIdempotentElem (1 : ZMod 1) := by simp [IsIdempotentElem]
  refine ⟨he, Bass.stableRangeCondition_one_corner he zeroRing_condition, ?_⟩
  apply Subtype.ext
  exact Subsingleton.elim _ _

end StableRangeTests.CornerClient
