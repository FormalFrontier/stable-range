/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.RowCompletionTwo
public import StableRangeTests.RowCompletionTwoFixtures
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

/-!
# Clients of explicit length-two completion and cancellation

The completed integer matrix and kernel coordinates are compared to the
independently checked arithmetic fixtures. The supplied product equivalence
is nonidentity; its original first projection is not the coordinate projection.
The cancellation client evaluates the nonidentity supplied equivalence at one.
-/

set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace StableRangeTests.RowCompletionTwoClient

open RowCompletionTwoFixtures

private def integerCompletion : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  Matrix.coefficientRowCompletionTwo ℤ row witness bezout

private theorem integerCompletion_matrix :
    (integerCompletion : Matrix (Fin 2) (Fin 2) ℤ) = completedMatrix := rfl

theorem integerCompletion_two_sided :
    (Matrix.coefficientRowCompletionTwo ℤ row witness bezout : Matrix (Fin 2) (Fin 2) ℤ) *
        inverseMatrix = 1 ∧
      inverseMatrix * Matrix.coefficientRowCompletionTwo ℤ row witness bezout = 1 := by
  change (integerCompletion : Matrix (Fin 2) (Fin 2) ℤ) * inverseMatrix = 1 ∧
    inverseMatrix * integerCompletion = 1
  rw [integerCompletion_matrix]
  exact matrix_two_sided

private theorem integerKernelVector_coordinate :
    Bass.coefficientRowKernelEquivTwo ℤ row witness bezout
      ⟨kernelVector, kernelVector_mem⟩ = 1 := by
  rw [Bass.coefficientRowKernelEquivTwo_apply]
  norm_num [witness, kernelVector]

private theorem integerKernelVector_from_scalar :
    ((Bass.coefficientRowKernelEquivTwo ℤ row witness bezout).symm 1).1 = kernelVector := by
  rw [Bass.coefficientRowKernelEquivTwo_symm_apply]
  ext i
  fin_cases i <;> norm_num [row, kernelVector]

private theorem integerCompletion_eq_fixture : integerCompletion = completedSL2 :=
  Subtype.ext integerCompletion_matrix

private def integerProduct : (Fin 2 → ℤ) ≃ₗ[ℤ] (ℤ × ℤ) :=
  (Matrix.SpecialLinearGroup.toLin' integerCompletion).trans (LinearEquiv.finTwoArrow ℤ ℤ)

private theorem integerProduct_eq_fixture : integerProduct = productEquiv := by
  simp [integerProduct, productEquiv, integerCompletion_eq_fixture]

private theorem integerProduct_first_projection : (integerProduct ![1, 0]).1 = 2 := by
  rw [integerProduct_eq_fixture]
  exact productEquiv_first_projection

private theorem integerProduct_nonidentity : (integerProduct ![1, 0]).1 ≠ (1 : ℤ) := by
  rw [integerProduct_eq_fixture]
  exact productEquiv_nonidentity

private noncomputable def integerCancellation : ℤ ≃ₗ[ℤ] ℤ :=
  LinearEquiv.coefficientProductCancellationTwo ℤ ℤ integerProduct

private theorem integerProduct_kernelVector : integerProduct kernelVector = (0, 1) := by
  apply Prod.ext
  · change LinearEquiv.coefficientRowCompletionTwo ℤ row witness bezout kernelVector 0 = 0
    rw [LinearEquiv.coefficientRowCompletionTwo_apply_zero]
    simpa only [LinearMap.mem_ker] using kernelVector_mem
  · change ((Matrix.coefficientRowCompletionTwo ℤ row witness bezout :
      Matrix (Fin 2) (Fin 2) ℤ) *ᵥ kernelVector) 1 = 1
    rw [Matrix.mulVec, Matrix.coefficientRowCompletionTwo_row_one]
    norm_num [witness, kernelVector, dotProduct, Fin.sum_univ_two]

private theorem integerProduct_witness : integerProduct witness = (1, 0) := by
  apply Prod.ext
  · change LinearEquiv.coefficientRowCompletionTwo ℤ row witness bezout witness 0 = 1
    rw [LinearEquiv.coefficientRowCompletionTwo_apply_zero,
      Bass.coefficientRowScalarMap_apply]
    norm_num [row, witness, dotProduct, Fin.sum_univ_two]
  · change LinearEquiv.coefficientRowCompletionTwo ℤ row witness bezout witness 1 = 0
    rw [LinearEquiv.coefficientRowCompletionTwo_apply_one]
    norm_num [witness]

private theorem integerCancellation_at_one : integerCancellation 1 = 1 := by
  have hkernel : integerProduct.symm (0, 1) = kernelVector := by
    apply integerProduct.injective
    rw [integerProduct.apply_symm_apply]
    exact integerProduct_kernelVector.symm
  have hwitness : integerProduct.symm (1, 0) = witness := by
    apply integerProduct.injective
    rw [integerProduct.apply_symm_apply]
    exact integerProduct_witness.symm
  change (LinearEquiv.coefficientProductCancellationTwo ℤ ℤ integerProduct) 1 = 1
  rw [LinearEquiv.coefficientProductCancellationTwo_apply, hkernel, hwitness]
  norm_num [witness, kernelVector]

private theorem integerCancellation_symm_at_one : integerCancellation.symm 1 = 1 := by
  rw [← integerCancellation_at_one]
  exact integerCancellation.symm_apply_apply 1

private def zeroCompletion : Matrix.SpecialLinearGroup (Fin 2) (ZMod 1) :=
  Matrix.coefficientRowCompletionTwo (ZMod 1) ![0, 0] ![0, 0]
    (Subsingleton.elim _ _)

private noncomputable def zeroCancellation : ZMod 1 ≃ₗ[ZMod 1] ZMod 1 :=
  LinearEquiv.coefficientProductCancellationTwo (ZMod 1) (ZMod 1)
    (LinearEquiv.finTwoArrow (ZMod 1) (ZMod 1))

private theorem zeroCancellation_apply : zeroCancellation (0 : ZMod 1) = 0 := by
  exact Subsingleton.elim _ _

universe v

private theorem universe_polymorphic_client {R : Type*} [CommRing R]
    {P : Type v} [AddCommGroup P] [Module R P]
    (e : (Fin 2 → R) ≃ₗ[R] (R × P)) (p : P) :
    let x := e.symm (0, p)
    let b := e.symm (1, 0)
    LinearEquiv.coefficientProductCancellationTwo R P e p =
      -b 1 * x 0 + b 0 * x 1 :=
  LinearEquiv.coefficientProductCancellationTwo_apply R P e p

end StableRangeTests.RowCompletionTwoClient
