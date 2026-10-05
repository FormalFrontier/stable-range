/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.RowKernel
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Independent length-two integer arithmetic

The coefficient witness, inverse-matrix equations, nonzero kernel vector,
and original first projection of a nonidentity product equivalence are
checked without using the length-two completion construction.
-/

set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace StableRangeTests.RowCompletionTwoFixtures

def row : Fin 2 → ℤ := ![2, 3]
def witness : Fin 2 → ℤ := ![-1, 1]

theorem bezout : row 0 * witness 0 + row 1 * witness 1 = 1 := by
  norm_num [row, witness]

theorem zeroIntegerRow_not_unimodular :
    ¬ Bass.IsRightUnimodular (![0, 0] : Fin 2 → ℤ) := by
  rintro ⟨coefficients, h⟩
  norm_num [Bass.IsRightUnimodular, dotProduct, Fin.sum_univ_succ] at h

def completedMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![2, 3; -1, -1]
def inverseMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![-1, -3; 1, 2]

theorem matrix_two_sided :
    completedMatrix * inverseMatrix = 1 ∧ inverseMatrix * completedMatrix = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [completedMatrix, inverseMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply]

def kernelVector : Fin 2 → ℤ := ![-3, 2]

theorem kernelVector_mem :
    kernelVector ∈ LinearMap.ker (Bass.coefficientRowScalarMap ℤ 2 row) := by
  simp [LinearMap.mem_ker, Bass.coefficientRowScalarMap_apply, row,
    kernelVector, dotProduct, Fin.sum_univ_succ]

theorem kernelVector_ne_zero : kernelVector ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [kernelVector] at this

def completedSL2 : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨completedMatrix, by norm_num [completedMatrix, Matrix.det_fin_two_of]⟩

def productEquiv : (Fin 2 → ℤ) ≃ₗ[ℤ] (ℤ × ℤ) :=
  (Matrix.SpecialLinearGroup.toLin' completedSL2).trans (LinearEquiv.finTwoArrow ℤ ℤ)

theorem productEquiv_original_first_projection (x : Fin 2 → ℤ) :
    (productEquiv x).1 = row ⬝ᵥ x := by
  change (Matrix.SpecialLinearGroup.toLin' completedSL2 x) 0 = row ⬝ᵥ x
  rw [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  change (completedSL2 : Matrix (Fin 2) (Fin 2) ℤ) 0 ⬝ᵥ x = row ⬝ᵥ x
  rfl

theorem productEquiv_first_projection : (productEquiv ![1, 0]).1 = 2 := by
  rw [productEquiv_original_first_projection]
  norm_num [row, dotProduct, Fin.sum_univ_succ]

theorem productEquiv_nonidentity : (productEquiv ![1, 0]).1 ≠ (1 : ℤ) := by
  rw [productEquiv_first_projection]
  norm_num

end StableRangeTests.RowCompletionTwoFixtures
