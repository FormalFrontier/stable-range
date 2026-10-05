/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.RowKernel
public import Mathlib.Data.ZMod.Basic

/-!
# Noncommutative coefficient-row fixtures

An explicit row over two-by-two integer matrices has a nonzero right kernel
and a nontrivial right coefficient order. The examples use only the existing
split-kernel API, independently of rectangular completion.
-/

set_option warningAsError true

@[expose] public section

namespace RightRowCompletionFixtures

open scoped Matrix

abbrev Coeff := Matrix (Fin 2) (Fin 2) ℤ

def e11 : Coeff := !![1, 0; 0, 0]
def e22 : Coeff := !![0, 0; 0, 1]
def e12 : Coeff := !![0, 1; 0, 0]

def row : Fin 2 → Coeff := ![e11, e22]
def witness : Fin 2 → Coeff := ![e11, e22]

private theorem e11_mul_e22 : e11 * e22 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e11, e22, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem e22_mul_e11 : e22 * e11 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e11, e22, Matrix.mul_apply, Fin.sum_univ_succ]

theorem e11_add_e22 : e11 + e22 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [e11, e22, Matrix.one_apply]

theorem e11_sq : e11 * e11 = e11 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e11, Matrix.mul_apply, Fin.sum_univ_succ]

theorem e22_sq : e22 * e22 = e22 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e22, Matrix.mul_apply, Fin.sum_univ_succ]

theorem row_apply (x : Fin 2 → Coeff) :
    dotProductBilin Coeff Coeffᵐᵒᵖ row x = e11 * x 0 + e22 * x 1 := by
  simp [dotProductBilin, dotProduct, Fin.sum_univ_succ, row]

theorem witness_spec : dotProductBilin Coeff Coeffᵐᵒᵖ row witness = 1 := by
  rw [row_apply]
  change e11 * e11 + e22 * e22 = 1
  rw [e11_sq, e22_sq, e11_add_e22]

def kernelColumn (t : Coeff) : Fin 2 → Coeff := ![e22 * t, e11 * t]

theorem kernelColumn_mem (t : Coeff) :
    kernelColumn t ∈ LinearMap.ker (dotProductBilin Coeff Coeffᵐᵒᵖ row) := by
  rw [LinearMap.mem_ker]
  rw [row_apply]
  change e11 * (e22 * t) + e22 * (e11 * t) = 0
  simp [← mul_assoc, e11_mul_e22, e22_mul_e11]

theorem kernelColumn_add (t s : Coeff) :
    kernelColumn (t + s) = kernelColumn t + kernelColumn s := by
  funext i
  fin_cases i <;> simp [kernelColumn, mul_add]

theorem kernelColumn_smul (t : Coeff) (s : Coeffᵐᵒᵖ) :
    kernelColumn (s • t) = s • kernelColumn t := by
  funext i
  fin_cases i <;> simp [kernelColumn, mul_assoc]

theorem kernelColumn_recover (t : Coeff) :
    kernelColumn t 0 + kernelColumn t 1 = t := by
  change e22 * t + e11 * t = t
  rw [← add_mul, add_comm e22 e11, e11_add_e22, one_mul]

theorem kernelColumn_reconstruct
    (x : LinearMap.ker (dotProductBilin Coeff Coeffᵐᵒᵖ row)) :
    kernelColumn (x.1 0 + x.1 1) = x.1 := by
  have hxy : e11 * x.1 0 + e22 * x.1 1 = 0 := by
    have hx := LinearMap.mem_ker.mp x.2
    simpa only [row_apply] using hx
  have hx0 : e11 * x.1 0 = 0 := by
    have h := congrArg (e11 * ·) hxy
    simpa only [mul_add, ← mul_assoc, e11_sq, e11_mul_e22,
      zero_mul, add_zero, mul_zero] using h
  have hx1 : e22 * x.1 1 = 0 := by
    have h := congrArg (e22 * ·) hxy
    simpa only [mul_add, ← mul_assoc, e22_sq, e22_mul_e11,
      zero_mul, zero_add, mul_zero] using h
  have hleft : e22 * x.1 0 = x.1 0 := by
    calc
      _ = (e11 + e22) * x.1 0 := by rw [add_mul, hx0, zero_add]
      _ = x.1 0 := by rw [e11_add_e22, one_mul]
  have hright : e11 * x.1 1 = x.1 1 := by
    calc
      _ = (e11 + e22) * x.1 1 := by rw [add_mul, hx1, add_zero]
      _ = x.1 1 := by rw [e11_add_e22, one_mul]
  funext i
  fin_cases i
  · simp [kernelColumn, mul_add, hleft, hx1]
  · simp [kernelColumn, mul_add, hx0, hright]

/-- Actual right-linear coordinates on the nonzero kernel of the matrix-ring row. -/
def kernelCoordinates :
    LinearMap.ker (dotProductBilin Coeff Coeffᵐᵒᵖ row) ≃ₗ[Coeffᵐᵒᵖ]
      (Fin 1 → Coeff) where
  toFun x := fun _ ↦ x.1 0 + x.1 1
  invFun t := ⟨kernelColumn (t 0), kernelColumn_mem (t 0)⟩
  left_inv x := Subtype.ext (kernelColumn_reconstruct x)
  right_inv t := by
    funext i
    fin_cases i
    exact kernelColumn_recover (t 0)
  map_add' x y := by
    funext i
    change (x.1 0 + y.1 0) + (x.1 1 + y.1 1) =
      (x.1 0 + x.1 1) + (y.1 0 + y.1 1)
    abel
  map_smul' s x := by
    funext i
    change (x.1 0 * s.unop) + (x.1 1 * s.unop) =
      (x.1 0 + x.1 1) * s.unop
    exact (add_mul _ _ _).symm

@[simp]
theorem kernelCoordinates_symm_apply (t : Coeff) :
    (kernelCoordinates.symm ![t]).1 = kernelColumn t := rfl

theorem kernelColumn_nonzero : kernelColumn 1 ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  have h22 : e22 = 0 := by simpa [kernelColumn] using h0
  have hentry := congrFun (congrFun h22 (1 : Fin 2)) (1 : Fin 2)
  norm_num [e22] at hentry

theorem row_order :
    dotProductBilin Coeff Coeffᵐᵒᵖ row ![e12, 0] = e12 ∧
    e12 * e11 = 0 := by
  constructor
  · rw [row_apply]
    change e11 * e12 + e22 * 0 = e12
    simp only [mul_zero, add_zero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [e11, e12, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [e11, e12, Matrix.mul_apply, Fin.sum_univ_succ]

def blockCompletion : Matrix (Fin 2) (Fin 2) Coeff :=
  !![e11, e22; e22, e11]

theorem blockCompletion_sq : blockCompletion * blockCompletion = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [blockCompletion, Matrix.mul_apply, Fin.sum_univ_succ,
      e11_sq, e22_sq, e11_mul_e22, e22_mul_e11, e11_add_e22,
      add_comm e22 e11]

theorem blockCompletion_row : blockCompletion 0 = row := by
  funext i
  fin_cases i <;> rfl

theorem empty_zero_ring : Bass.IsRightUnimodular (Fin.elim0 : Fin 0 → ZMod 1) := by
  refine ⟨Fin.elim0, ?_⟩
  exact Subsingleton.elim _ _

theorem empty_nonzero_ring :
    ¬ Bass.IsRightUnimodular (Fin.elim0 : Fin 0 → ℤ) := by
  rintro ⟨b, hb⟩
  simp at hb

theorem singleton_unit : Bass.IsRightUnimodular (![1] : Fin 1 → ℤ) := by
  refine ⟨![1], ?_⟩
  norm_num [dotProductBilin, dotProduct, Fin.sum_univ_succ]

theorem unequal_zero_ring_completion :
    ∃ (A : Matrix (Fin 2) (Fin 0) (ZMod 1))
      (B : Matrix (Fin 0) (Fin 2) (ZMod 1)),
        A 0 = Fin.elim0 ∧ A * B = 1 ∧ B * A = 1 := by
  refine ⟨0, 0, ?_, ?_, ?_⟩ <;> exact Subsingleton.elim _ _

end RightRowCompletionFixtures
