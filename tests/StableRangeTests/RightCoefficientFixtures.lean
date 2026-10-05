/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Right-coefficient row fixtures

Integer and matrix rows test the right-hand multiplication order, explicit
right witnesses and the original row projection. Empty and zero rows record
the degenerate cases without appealing to split-kernel existence.
-/

set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace StableRangeTests.RightCoefficientFixtures

def integerRow : Fin 2 → ℤ := ![2, 3]
def integerWitness : Fin 2 → ℤ := ![-1, 1]

theorem integerWitness_rightInverse :
    dotProductBilin ℤ ℤᵐᵒᵖ integerRow integerWitness = 1 := by
  norm_num [integerRow, integerWitness, dotProductBilin, dotProduct,
    Fin.sum_univ_succ]

theorem integerRow_unimodular : Bass.IsRightUnimodular integerRow :=
  ⟨integerWitness, integerWitness_rightInverse⟩

theorem integerRow_on_witness (y : ℤ) :
    dotProductBilin ℤ ℤᵐᵒᵖ integerRow
      (fun i ↦ integerWitness i * y) = y := by
  norm_num [integerRow, integerWitness, dotProductBilin, dotProduct,
    Fin.sum_univ_succ]
  ring

theorem integerRow_surjective :
    Function.Surjective (dotProductBilin ℤ ℤᵐᵒᵖ integerRow) :=
  fun y ↦ ⟨fun i ↦ integerWitness i * y, integerRow_on_witness y⟩

theorem integerOriginalRow (x : Fin 2 → ℤ) :
    dotProductBilin ℤ ℤᵐᵒᵖ integerRow x = 2 * x 0 + 3 * x 1 := by
  simp [integerRow, dotProductBilin, dotProduct, Fin.sum_univ_succ]

/-- A nonzero vector in the kernel of the integer row. -/
def integerKernelVector : Fin 2 → ℤ := ![3, -2]

theorem integerKernelVector_mem_ker :
    integerKernelVector ∈ LinearMap.ker (dotProductBilin ℤ ℤᵐᵒᵖ integerRow) := by
  apply LinearMap.mem_ker.mpr
  rw [integerOriginalRow]
  norm_num [integerKernelVector]

theorem integerKernelVector_ne_zero : integerKernelVector ≠ 0 := by
  intro hzero
  have hcoordinate := congrArg (fun x : Fin 2 → ℤ ↦ x 0) hzero
  norm_num [integerKernelVector] at hcoordinate

theorem zeroIntegerRow_not_unimodular :
    ¬ Bass.IsRightUnimodular (![0, 0] : Fin 2 → ℤ) := by
  rintro ⟨witness, hwitness⟩
  norm_num [Fin.sum_univ_succ] at hwitness

theorem zeroIntegerRow_not_surjective :
    ¬ Function.Surjective
      (dotProductBilin ℤ ℤᵐᵒᵖ (![0, 0] : Fin 2 → ℤ)) := by
  intro hsurjective
  obtain ⟨witness, hwitness⟩ := hsurjective 1
  norm_num [dotProductBilin, dotProduct, Fin.sum_univ_succ] at hwitness

theorem zeroIntegerRow_not_one_mem_rightSpan :
    (1 : ℤ) ∉ Submodule.span ℤᵐᵒᵖ (Set.range (![0, 0] : Fin 2 → ℤ)) := by
  intro hone
  obtain ⟨coefficient, hcoefficient⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℤᵐᵒᵖ).mp hone
  norm_num [Fin.sum_univ_succ] at hcoefficient

theorem emptyIntegerRow_not_unimodular :
    ¬ Bass.IsRightUnimodular (Fin.elim0 : Fin 0 → ℤ) := by
  rintro ⟨_, hwitness⟩
  norm_num at hwitness

theorem emptyZeroRingRow_unimodular :
    Bass.IsRightUnimodular (Fin.elim0 : Fin 0 → ZMod 1) :=
  ⟨Fin.elim0, Subsingleton.elim _ _⟩

def matrixE11 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]
def matrixE22 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 0, 1]
def matrixE12 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]
def matrixRow : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ := ![matrixE11, matrixE22]
def matrixWitness : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ := ![1, 1]

theorem matrixWitness_rightInverse :
    dotProductBilin (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ
      matrixRow matrixWitness = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixRow, matrixWitness, matrixE11, matrixE22,
      dotProductBilin, dotProduct, Fin.sum_univ_succ,
      Matrix.mul_apply, Matrix.one_apply]

theorem matrixRow_unimodular : Bass.IsRightUnimodular matrixRow :=
  ⟨matrixWitness, matrixWitness_rightInverse⟩

theorem matrixRow_on_E12 :
    dotProductBilin (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ
      matrixRow (![matrixE12, 0] : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ) =
      matrixE12 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixRow, matrixE11, matrixE22, matrixE12,
      dotProductBilin, dotProduct, Fin.sum_univ_succ,
      Matrix.mul_apply]

theorem reversedRow_on_E12 :
    (∑ i : Fin 2, (![matrixE12, 0] : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ) i *
      matrixRow i) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixRow, matrixE11, matrixE22, matrixE12,
      Fin.sum_univ_succ, Matrix.mul_apply]

theorem matrixOrder_differs :
    dotProductBilin (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ
        matrixRow (![matrixE12, 0] : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ) ≠
      ∑ i : Fin 2, (![matrixE12, 0] : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ) i *
        matrixRow i := by
  rw [matrixRow_on_E12, reversedRow_on_E12]
  intro heq
  have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ ↦ m 0 1) heq
  norm_num [matrixE12] at h

end StableRangeTests.RightCoefficientFixtures
