/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.LinearAlgebra.Matrix.Notation

/-! Stable-range-one elementary generation at finite-rank boundaries. -/

set_option warningAsError true

@[expose] public section

namespace StableRangeTests.ElementaryGenerationClient

open Matrix.GeneralLinearGroup

universe u

variable {R : Type u} [CommRing R]

private theorem empty_rank (matrix : GL (Fin 0) R) :
    ∃ (left right : elementarySubgroup (Fin 0) R) (diagonal : Fin 0 → Rˣ),
      (left : GL (Fin 0) R) * matrix * (right : GL (Fin 0) R) =
        diagonalUnit diagonal := by
  refine ⟨1, 1, (fun index => index.elim0), ?_⟩
  apply Units.ext
  ext index
  exact index.elim0

/-- An invertible rank-one matrix over a commutative ring already has a unit
leading entry. -/
public theorem rank_one_pivot (matrix : GL (Fin 1) R) :
    ∃ factor : elementarySubgroup (Fin 1) R,
      IsUnit (((((factor : GL (Fin 1) R) * matrix) : GL (Fin 1) R) :
        Matrix (Fin 1) (Fin 1) R) 0 0) := by
  refine ⟨1, ?_⟩
  have hdet : IsUnit ((matrix : Matrix (Fin 1) (Fin 1) R).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit matrix)
  simpa only [OneMemClass.coe_one, one_mul, Matrix.det_fin_one] using hdet

private theorem zero_ring_pivot (rank : ℕ)
    (matrix : GL (Fin (rank + 1)) (ZMod 1)) :
    ∃ factor : elementarySubgroup (Fin (rank + 1)) (ZMod 1),
      IsUnit (((((factor : GL (Fin (rank + 1)) (ZMod 1)) * matrix) :
        GL (Fin (rank + 1)) (ZMod 1)) :
          Matrix (Fin (rank + 1)) (Fin (rank + 1)) (ZMod 1)) 0 0) := by
  refine ⟨1, ?_⟩
  have h : ((matrix : Matrix (Fin (rank + 1)) (Fin (rank + 1)) (ZMod 1)) 0 0) = 1 :=
    Subsingleton.elim _ _
  simpa only [OneMemClass.coe_one, one_mul, h] using (isUnit_one : IsUnit (1 : ZMod 1))

section ProductOfFields

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private abbrev Coefficients := ZMod 2 × ZMod 2

private def firstIdempotent : Coefficients := (1, 0)
private def secondIdempotent : Coefficients := (0, 1)

private theorem first_nonunit : ¬ IsUnit firstIdempotent := by
  simp [firstIdempotent]

private theorem second_nonunit : ¬ IsUnit secondIdempotent := by
  simp [secondIdempotent]

private theorem nonlocal : ¬ IsLocalRing Coefficients := by
  intro hlocal
  have hnonunit : ¬ IsUnit (firstIdempotent + secondIdempotent) :=
    @IsLocalRing.nonunits_add Coefficients _ hlocal _ _ first_nonunit second_nonunit
  apply hnonunit
  have hsum : firstIdempotent + secondIdempotent = 1 := by
    decide
  simpa only [hsum] using (isUnit_one : IsUnit (1 : Coefficients))

private theorem product_condition : Bass.StableRangeCondition Coefficients 1 :=
  Bass.stableRangeCondition_one_of_krullDimLE_zero

/-- An invertible determinant-one matrix over a nonlocal product of fields,
with neither entry in its first column a unit. -/
private def productMatrix : GL (Fin 2) Coefficients where
  val := !![firstIdempotent, -secondIdempotent;
    secondIdempotent, firstIdempotent]
  inv := !![firstIdempotent, secondIdempotent;
    -secondIdempotent, firstIdempotent]
  val_inv := by
    ext row column <;> fin_cases row <;> fin_cases column <;> decide
  inv_val := by
    ext row column <;> fin_cases row <;> fin_cases column <;> decide

private theorem productMatrix_det : Matrix.GeneralLinearGroup.det productMatrix = 1 := by
  apply Units.ext
  simp [productMatrix, Matrix.det_fin_two, Matrix.of_apply,
    firstIdempotent, secondIdempotent, Prod.ext_iff]

private theorem productMatrix_first_column_nonunit :
    ¬ IsUnit ((productMatrix : Matrix (Fin 2) (Fin 2) Coefficients) 0 0) ∧
    ¬ IsUnit ((productMatrix : Matrix (Fin 2) (Fin 2) Coefficients) 1 0) := by
  simpa [productMatrix, Matrix.of_apply] using And.intro first_nonunit second_nonunit

private theorem existing_shear_creates_unit_pivot :
    ∃ factor : elementarySubgroup (Fin 2) Coefficients,
      (((factor : GL (Fin 2) Coefficients) * productMatrix : GL (Fin 2) Coefficients) :
        Matrix (Fin 2) (Fin 2) Coefficients) 0 0 = 1 := by
  let shear : GL (Fin 2) Coefficients := elementaryUnit 0 1 (by decide) secondIdempotent
  refine ⟨⟨shear, elementaryUnit_mem (0 : Fin 2) (1 : Fin 2) (by decide)
    secondIdempotent⟩, ?_⟩
  simp [shear, productMatrix, firstIdempotent, secondIdempotent,
    Matrix.add_mul, Matrix.single_mul_apply_same, Prod.ext_iff, Matrix.of_apply]

private theorem product_nonvacuity :
    Bass.StableRangeCondition Coefficients 1 ∧
    ¬ IsLocalRing Coefficients ∧
    Matrix.GeneralLinearGroup.det productMatrix = 1 ∧
    ¬ IsUnit ((productMatrix : Matrix (Fin 2) (Fin 2) Coefficients) 0 0) ∧
    ¬ IsUnit ((productMatrix : Matrix (Fin 2) (Fin 2) Coefficients) 1 0) ∧
    ∃ factor : elementarySubgroup (Fin 2) Coefficients,
      IsUnit (((((factor : GL (Fin 2) Coefficients) * productMatrix) :
        GL (Fin 2) Coefficients) : Matrix (Fin 2) (Fin 2) Coefficients) 0 0) := by
  obtain ⟨hfirst, hsecond⟩ := productMatrix_first_column_nonunit
  obtain ⟨factor, hpivot⟩ := existing_shear_creates_unit_pivot
  exact ⟨product_condition, nonlocal, productMatrix_det, hfirst, hsecond,
    factor, hpivot.symm ▸ isUnit_one⟩

end ProductOfFields

section TheoremApplications

private theorem local_pivot [IsLocalRing R] {rank : ℕ}
    (matrix : GL (Fin (rank + 1)) R) :
    ∃ factor : elementarySubgroup (Fin (rank + 1)) R,
      IsUnit (((((factor : GL (Fin (rank + 1)) R) * matrix) :
        GL (Fin (rank + 1)) R) : Matrix (Fin (rank + 1)) (Fin (rank + 1)) R) 0 0) :=
  exists_elementary_unit_pivot_of_stableRangeCondition_one
    Bass.stableRangeCondition_one_of_isLocalRing matrix

private theorem productMatrix_pivot_from_stable_range :
    ∃ factor : elementarySubgroup (Fin 2) Coefficients,
      IsUnit (((((factor : GL (Fin 2) Coefficients) * productMatrix) :
        GL (Fin 2) Coefficients) : Matrix (Fin 2) (Fin 2) Coefficients) 0 0) ∧
      ¬ IsUnit ((productMatrix : Matrix (Fin 2) (Fin 2) Coefficients) 0 0) := by
  obtain ⟨factor, hpivot⟩ :=
    exists_elementary_unit_pivot_of_stableRangeCondition_one
      product_condition productMatrix
  exact ⟨factor, hpivot, productMatrix_first_column_nonunit.1⟩

private theorem productMatrix_diagonalization :
    ∃ (left right : elementarySubgroup (Fin 2) Coefficients)
      (diagonal : Fin 2 → Coefficientsˣ),
      (left : GL (Fin 2) Coefficients) * productMatrix *
        (right : GL (Fin 2) Coefficients) = diagonalUnit diagonal :=
  exists_elementary_diagonalization_of_stableRangeCondition_one
    product_condition productMatrix

private theorem boolean_index_diagonalization
    (matrix : GL Bool Coefficients) :
    ∃ (left right : elementarySubgroup Bool Coefficients)
      (diagonal : Bool → Coefficientsˣ),
      (left : GL Bool Coefficients) * matrix * (right : GL Bool Coefficients) =
        diagonalUnit diagonal :=
  exists_elementary_diagonalization_finite_of_stableRangeCondition_one
    product_condition matrix

end TheoremApplications

end StableRangeTests.ElementaryGenerationClient
