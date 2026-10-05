/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import StableRange.SquareRightRowCompletionCriterion
import StableRangeTests.SquareRightRowCompletionFixtures

/-!
# Free right-kernel criterion clients

The kernel-freeness criteria are instantiated on a unary integer row and a
noncommutative matrix-ring row with a nonzero kernel. The examples exercise
the original row and supplied inverse column through their matrix actions.
-/

set_option warningAsError true

open scoped Matrix
open RightRowCompletionFixtures SquareRightRowCompletionFixtures

example :
    ∃ (b : Fin 1 → ℤ) (g : Matrix.GeneralLinearGroup (Fin 1) ℤ),
      (g : Matrix (Fin 1) (Fin 1) ℤ) 0 = (![1] : Fin 1 → ℤ) ∧
      (fun i ↦ (g⁻¹).val i 0) = b ∧
      ((g : Matrix (Fin 1) (Fin 1) ℤ) *ᵥ ![2]) 0 = 2 ∧
      (g⁻¹).val *ᵥ Pi.single 0 1 = b := by
  obtain ⟨b, hb⟩ := singleton_unit
  obtain ⟨g, hrow, hcolumn⟩ :=
    (Matrix.free_rightCoefficientKernel_iff_exists_gl ℤ
      (![1] : Fin 1 → ℤ) b hb).mp integer_unary_kernel_free
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
  obtain ⟨g, hrow, hcolumn⟩ :=
    (Matrix.free_rightCoefficientKernel_iff_exists_gl Coeff
      row witness witness_spec).mp matrix_kernel_free
  refine ⟨g, hrow, hcolumn, ?_, ?_, kernelColumn_nonzero⟩
  · change (g : Matrix (Fin 2) (Fin 2) Coeff) 0 ⬝ᵥ ![e12, 0] = e12
    rw [hrow]
    exact row_order.1
  · funext i
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun hcolumn i

example :
    Bass.IsRightUnimodular row ∧
      Module.Free Coeffᵐᵒᵖ
        (LinearMap.ker (dotProductBilin Coeff Coeffᵐᵒᵖ row)) := by
  exact (Matrix.isRightUnimodular_and_free_kernel_iff_exists_gl Coeff row).mpr
    ⟨⟨blockCompletion, blockCompletion, blockCompletion_sq, blockCompletion_sq⟩,
      blockCompletion_row⟩
