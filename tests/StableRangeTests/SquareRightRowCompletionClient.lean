/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import StableRange.SquareRightRowCompletion
import StableRangeTests.SquareRightRowCompletionFixtures

/-!
# Square right-row completion clients

These examples use both actions of explicit square completions on nonzero
integer and noncommutative matrix-ring rows. The empty and unary boundaries
use genuine IBN and freeness data.
-/

set_option warningAsError true

open scoped Matrix
open RightRowCompletionFixtures SquareRightRowCompletionFixtures

example :
    ((Matrix.rightRowCompletionGL Coeff row witness witness_spec kernelCoordinates :
        Matrix (Fin 2) (Fin 2) Coeff) *ᵥ ![e12, 0]) 0 = e12 := by
  rw [Matrix.rightRowCompletionGL_mulVec,
    LinearEquiv.rightCoefficientRowCoordinates_zero]
  exact row_order.1

example :
    ((Matrix.rightRowCompletionGL Coeff row witness witness_spec
        kernelCoordinates)⁻¹).val *ᵥ Fin.cons 0 ![1] = kernelColumn 1 := by
  funext i
  rw [Matrix.rightRowCompletionGL_inv_mulVec]
  simp only [Fin.cons_zero, Fin.tail_cons, mul_zero, zero_add]
  exact congrFun (kernelCoordinates_symm_apply 1) i

example :
    (Matrix.rightRowCompletionGL Coeff row witness witness_spec kernelCoordinates :
      Matrix (Fin 2) (Fin 2) Coeff) 0 = row :=
  Matrix.rightRowCompletionGL_zero Coeff row witness witness_spec kernelCoordinates

example :
    (fun i ↦ ((Matrix.rightRowCompletionGL Coeff row witness witness_spec
      kernelCoordinates)⁻¹).val i 0) = witness :=
  Matrix.rightRowCompletionGL_inv_zero Coeff row witness witness_spec kernelCoordinates

example :
    ∃ (b : Fin 1 → ℤ) (g : Matrix.GeneralLinearGroup (Fin 1) ℤ),
      (g : Matrix (Fin 1) (Fin 1) ℤ) 0 = (![1] : Fin 1 → ℤ) ∧
      (fun i ↦ (g⁻¹).val i 0) = b ∧
      ((g : Matrix (Fin 1) (Fin 1) ℤ) *ᵥ ![2]) 0 = 2 ∧
      (g⁻¹).val *ᵥ Pi.single 0 1 = b := by
  obtain ⟨b, hb⟩ := singleton_unit
  let g := Matrix.rightRowCompletionGLOfFree ℤ
    (![1] : Fin 1 → ℤ) b hb integer_unary_kernel_free
  have hrow : (g : Matrix (Fin 1) (Fin 1) ℤ) 0 = (![1] : Fin 1 → ℤ) :=
    Matrix.rightRowCompletionGLOfFree_zero ℤ _ b hb integer_unary_kernel_free
  have hcolumn : (fun i ↦ (g⁻¹).val i 0) = b :=
    Matrix.rightRowCompletionGLOfFree_inv_zero ℤ _ b hb integer_unary_kernel_free
  refine ⟨b, g, hrow, hcolumn, ?_, ?_⟩
  · change (g : Matrix (Fin 1) (Fin 1) ℤ) 0 ⬝ᵥ ![2] = 2
    rw [hrow]
    norm_num [dotProduct, Fin.sum_univ_succ]
  · funext i
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun hcolumn i

example :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) Coeff,
      (g : Matrix (Fin 2) (Fin 2) Coeff) 0 = row ∧
      (fun i ↦ (g⁻¹).val i 0) = witness ∧
      ((g : Matrix (Fin 2) (Fin 2) Coeff) *ᵥ ![e12, 0]) 0 = e12 ∧
      (g⁻¹).val *ᵥ Pi.single 0 1 = witness ∧
      kernelColumn (1 : Coeff) ≠ 0 := by
  let g := Matrix.rightRowCompletionGLOfFree Coeff
    row witness witness_spec matrix_kernel_free
  have hrow : (g : Matrix (Fin 2) (Fin 2) Coeff) 0 = row :=
    Matrix.rightRowCompletionGLOfFree_zero Coeff row witness witness_spec matrix_kernel_free
  have hcolumn : (fun i ↦ (g⁻¹).val i 0) = witness :=
    Matrix.rightRowCompletionGLOfFree_inv_zero Coeff row witness witness_spec matrix_kernel_free
  refine ⟨g, hrow, hcolumn, ?_, ?_, kernelColumn_nonzero⟩
  · change (g : Matrix (Fin 2) (Fin 2) Coeff) 0 ⬝ᵥ ![e12, 0] = e12
    rw [hrow]
    exact row_order.1
  · funext i
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun hcolumn i

example : ¬ Bass.IsRightUnimodular (Fin.elim0 : Fin 0 → Coeff) := by
  exact empty_not_rightUnimodular Coeff
