/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Two-by-two matrix projection fixtures

Complementary projections give a right-unimodular pair and an explicit
right-sided shortening over any ring. Their nonunit properties additionally
require a nontrivial coefficient ring.

## References

* Mathlib, `LinearAlgebra.Matrix.Notation` (explicit projection matrices).
-/

set_option warningAsError true

@[expose] public section

namespace StableRangeTests.MatrixFixtures

universe u

variable {R : Type u} [Ring R]

def firstProjection : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, 0]
def secondProjection : Matrix (Fin 2) (Fin 2) R := !![0, 0; 0, 1]

theorem projections_sum :
    (firstProjection : Matrix (Fin 2) (Fin 2) R) + secondProjection = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [firstProjection, secondProjection, Matrix.of_apply]

theorem firstProjection_idempotent :
    (firstProjection : Matrix (Fin 2) (Fin 2) R) * firstProjection = firstProjection := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [firstProjection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]

theorem secondProjection_idempotent :
    (secondProjection : Matrix (Fin 2) (Fin 2) R) * secondProjection = secondProjection := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [secondProjection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]

theorem firstProjection_nonunit [Nontrivial R] :
    ¬ IsUnit (firstProjection : Matrix (Fin 2) (Fin 2) R) := by
  intro hunit
  obtain ⟨inverse, hright, _⟩ := isUnit_iff_exists.mp hunit
  have hentry := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) R => matrix 1 1) hright
  simp [firstProjection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply] at hentry

theorem secondProjection_nonunit [Nontrivial R] :
    ¬ IsUnit (secondProjection : Matrix (Fin 2) (Fin 2) R) := by
  intro hunit
  obtain ⟨inverse, hright, _⟩ := isUnit_iff_exists.mp hunit
  have hentry := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) R => matrix 0 0) hright
  simp [secondProjection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply] at hentry

theorem projections_right_witness :
    (firstProjection : Matrix (Fin 2) (Fin 2) R) * firstProjection +
      secondProjection * secondProjection = 1 := by
  simpa only [firstProjection_idempotent, secondProjection_idempotent] using
    (projections_sum (R := R))

theorem projections_unimodular :
    Bass.IsRightUnimodularCons (firstProjection : Matrix (Fin 2) (Fin 2) R)
      (fun _ : Fin 1 => secondProjection) := by
  refine ⟨firstProjection, fun _ => secondProjection, ?_⟩
  simpa only [Fin.sum_univ_one] using (projections_right_witness (R := R))

theorem projections_shortening :
    (secondProjection : Matrix (Fin 2) (Fin 2) R) -
      firstProjection * (-1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  calc
    secondProjection - firstProjection * (-1 : Matrix (Fin 2) (Fin 2) R) =
        secondProjection + firstProjection := by simp
    _ = firstProjection + secondProjection := add_comm _ _
    _ = 1 := projections_sum

end StableRangeTests.MatrixFixtures
