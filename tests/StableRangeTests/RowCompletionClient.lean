/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.RowCompletion
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Row-completion clients

The unimodular witness and both inverse matrix identities for an integer row
are verified directly. The first-row equivalence and matrix APIs are exercised
separately, as are the zero-ring boundary and the dimension-bound specialization.
-/

set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace StableRangeTests.RowCompletionClient

/-- A non-coordinate unimodular integer row. -/
def integerRow : Fin 3 → ℤ := ![2, 3, 0]

private theorem integerRow_unimodular : Bass.IsRightUnimodular integerRow := by
  refine ⟨![-1, 1, 0], ?_⟩
  norm_num [Bass.IsRightUnimodular, integerRow, dotProduct, Fin.sum_univ_succ]

private theorem zeroIntegerRow_not_unimodular :
    ¬ Bass.IsRightUnimodular (![0, 0, 0] : Fin 3 → ℤ) := by
  rintro ⟨witness, witness_sum⟩
  norm_num [dotProduct, Fin.sum_univ_succ] at witness_sum

private def integerMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![2, 3, 0; -1, -1, 0; 0, 0, 1]

private def integerInverse : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-1, -3, 0; 1, 2, 0; 0, 0, 1]

private theorem integerMatrix_row_zero : integerMatrix 0 = integerRow := by
  decide

private theorem integerMatrix_two_sided :
    integerMatrix * integerInverse = 1 ∧ integerInverse * integerMatrix = 1 := by
  constructor <;> ext index column <;>
    fin_cases index <;> fin_cases column <;>
    norm_num [integerMatrix, integerInverse, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply]

private theorem integerStableRange : Bass.StableRangeCondition ℤ 2 :=
  Bass.stableRangeCondition_succ_of_krullDimLE (R := ℤ) (d := 1)

private noncomputable def integerCompletion :
    (Fin 3 → ℤ) ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  LinearEquiv.coefficientRowCompletionOfStableRangeCondition
    ℤ 2 integerRow integerRow_unimodular integerStableRange (by decide)

private theorem integerCompletion_coordinate (x : Fin 3 → ℤ) :
    integerCompletion x 0 = integerRow ⬝ᵥ x :=
  LinearEquiv.coefficientRowCompletionOfStableRangeCondition_apply_zero
    ℤ 2 integerRow integerRow_unimodular integerStableRange (by decide) x

private noncomputable def integerDimensionCompletion :
    (Fin 3 → ℤ) ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  LinearEquiv.coefficientRowCompletionOfKrullDimLE ℤ 2 integerRow
    integerRow_unimodular (d := 1) (by decide)

private theorem integerCompletedMatrix_row :
    Matrix.coefficientRowCompletionOfStableRangeCondition ℤ 2 integerRow
      integerRow_unimodular integerStableRange (by decide) 0 = integerRow :=
  Matrix.coefficientRowCompletionOfStableRangeCondition_row_zero _ _ _ _ _ _

private theorem integerCompletedMatrix_two_sided :
    Matrix.coefficientRowCompletionOfStableRangeCondition ℤ 2 integerRow
        integerRow_unimodular integerStableRange (by decide) *
      Matrix.coefficientRowCompletionInverseOfStableRangeCondition ℤ 2 integerRow
        integerRow_unimodular integerStableRange (by decide) = 1 ∧
    Matrix.coefficientRowCompletionInverseOfStableRangeCondition ℤ 2 integerRow
        integerRow_unimodular integerStableRange (by decide) *
      Matrix.coefficientRowCompletionOfStableRangeCondition ℤ 2 integerRow
        integerRow_unimodular integerStableRange (by decide) = 1 :=
  ⟨Matrix.coefficientRowCompletion_mul_inverse _ _ _ _ _ _,
    Matrix.coefficientRowCompletion_inverse_mul _ _ _ _ _ _⟩

private def zeroRow : Fin 1 → ZMod 1 := fun _ ↦ 0

private theorem zeroRow_unimodular : Bass.IsRightUnimodular zeroRow :=
  ⟨fun _ ↦ 0, Subsingleton.elim _ _⟩

private theorem zeroRingStableRange : Bass.StableRangeCondition (ZMod 1) 0 := by
  intro _ _ _
  exact ⟨fun index ↦ Fin.elim0 index, ⟨fun index ↦ Fin.elim0 index,
    Subsingleton.elim _ _⟩⟩

private noncomputable def zeroRingCompletion :
    (Fin 1 → ZMod 1) ≃ₗ[ZMod 1] (Fin 1 → ZMod 1) :=
  LinearEquiv.coefficientRowCompletionOfStableRangeCondition
    (ZMod 1) 0 zeroRow zeroRow_unimodular zeroRingStableRange (by decide)

private theorem zeroRingCompletedMatrix_row :
    Matrix.coefficientRowCompletionOfStableRangeCondition (ZMod 1) 0 zeroRow
      zeroRow_unimodular zeroRingStableRange (by decide) 0 = zeroRow :=
  Matrix.coefficientRowCompletionOfStableRangeCondition_row_zero _ _ _ _ _ _

end StableRangeTests.RowCompletionClient
