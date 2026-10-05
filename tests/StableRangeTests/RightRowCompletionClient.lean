/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import StableRange.RightRowCompletion
import StableRangeTests.RightRowCompletionFixtures

/-!
# Rectangular row-completion clients

The right-linear completion preserves the actual matrix-ring row action on a
noncentral input, and its tail and inverse reconstruct a nonzero kernel column.
Its converse reads kernel coordinates from a concrete self-inverse completion,
also in the empty-tail boundary.
-/

set_option warningAsError true

open scoped Matrix
open RightRowCompletionFixtures

example :
    (Matrix.rightRowCompletion Coeff row witness witness_spec kernelCoordinates *ᵥ
        ![e12, 0]) 0 = e12 := by
  rw [Matrix.rightRowCompletion_mulVec,
    LinearEquiv.rightCoefficientRowCoordinates_zero]
  exact row_order.1

example :
    Matrix.rightRowCompletion Coeff row witness witness_spec kernelCoordinates *
        Matrix.rightRowCompletionInv Coeff row witness witness_spec kernelCoordinates = 1 :=
  Matrix.rightRowCompletion_mul_inv Coeff row witness witness_spec kernelCoordinates

example :
    (Matrix.rightRowCompletion Coeff row witness witness_spec kernelCoordinates *ᵥ
        kernelColumn 1) (Fin.succ 0) = 1 := by
  rw [Matrix.rightRowCompletion_mulVec,
    LinearEquiv.rightCoefficientRowCoordinates_succ_projection]
  have hprojection :
      (⟨kernelColumn 1 - (fun i ↦ witness i *
          dotProductBilin Coeff Coeffᵐᵒᵖ row (kernelColumn 1)),
        LinearEquiv.rightCoefficientKernelProd_symm_fst_mem
          Coeff row witness witness_spec (kernelColumn 1)⟩ :
        LinearMap.ker (dotProductBilin Coeff Coeffᵐᵒᵖ row)) =
          ⟨kernelColumn 1, kernelColumn_mem 1⟩ := by
    apply Subtype.ext
    funext i
    simp [LinearMap.mem_ker.mp (kernelColumn_mem 1)]
  rw [hprojection]
  exact kernelColumn_recover 1

example :
    Matrix.rightRowCompletionInv Coeff row witness witness_spec kernelCoordinates *ᵥ
      Fin.cons 0 ![1] = kernelColumn 1 := by
  funext i
  rw [Matrix.rightRowCompletionInv_mulVec,
    LinearEquiv.rightCoefficientRowCoordinates_symm_apply]
  simp only [Fin.cons_zero, Fin.tail_cons, mul_zero, zero_add,
    kernelCoordinates_symm_apply]

example : Bass.IsRightUnimodular row :=
  Matrix.isRightUnimodular_of_rectangular_inverse Coeff row
    blockCompletion blockCompletion blockCompletion_row blockCompletion_sq

example : Module.Finite Coeffᵐᵒᵖ
    (LinearMap.ker (dotProductBilin Coeff Coeffᵐᵒᵖ row)) :=
  LinearMap.finite_rightCoefficientKernel Coeff row ⟨witness, witness_spec⟩

example (t : Coeff) :
    (LinearEquiv.rightCoefficientKernelEquivOfMatrixInverse Coeff row
      blockCompletion blockCompletion blockCompletion_row blockCompletion_sq
      blockCompletion_sq ⟨kernelColumn t, kernelColumn_mem t⟩) 0 = t := by
  rw [LinearEquiv.rightCoefficientKernelEquivOfMatrixInverse_apply]
  have h : (Fin.tail (blockCompletion *ᵥ kernelColumn t)) 0 =
      e22 * (e22 * t) + e11 * (e11 * t) := by
    simp [blockCompletion, kernelColumn, dotProduct, Fin.sum_univ_succ]
  rw [h, ← mul_assoc, e22_sq, ← mul_assoc, e11_sq, ← add_mul,
    add_comm e22 e11, e11_add_e22, one_mul]

noncomputable example :
    LinearMap.ker (dotProductBilin ℤ ℤᵐᵒᵖ (![1] : Fin 1 → ℤ))
      ≃ₗ[ℤᵐᵒᵖ] (Fin 0 → ℤ) :=
  LinearEquiv.rightCoefficientKernelEquivOfMatrixInverse ℤ ![1] 1 1
    (by
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      simp) (by simp) (by simp)

example :
    Bass.IsRightUnimodular row ∧
      Module.Free Coeffᵐᵒᵖ (LinearMap.ker (dotProductBilin Coeff Coeffᵐᵒᵖ row)) :=
  (Matrix.isRightUnimodular_and_free_kernel_iff_exists_rectangular_inverse
    Coeff row).mpr
    ⟨1, blockCompletion, blockCompletion, blockCompletion_row,
      blockCompletion_sq, blockCompletion_sq⟩

example :
    ∃ (m : ℕ) (A : Matrix (Fin (m + 1)) (Fin 0) (ZMod 1))
      (B : Matrix (Fin 0) (Fin (m + 1)) (ZMod 1)),
        A 0 = Fin.elim0 ∧ A * B = 1 ∧ B * A = 1 :=
  (Matrix.isRightUnimodular_and_free_kernel_iff_exists_rectangular_inverse
    (ZMod 1) (Fin.elim0 : Fin 0 → ZMod 1)).mp
    ⟨empty_zero_ring, by infer_instance⟩
