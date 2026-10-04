/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Elementary generation clients

These clients test finite determinant generation and the stable elementary
quotient under stable range one using explicit coefficient rings.

## References

* Mathlib, `Data.ZMod.Basic`, `Algebra.Field.ZMod` and
  `LinearAlgebra.Matrix.Notation` (finite-ring and matrix fixtures).
-/

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

private theorem empty_determinant_generation (stable : Bass.StableRangeCondition R 1)
    (matrix : GL (Fin 0) R) : matrix ∈ elementarySubgroup (Fin 0) R := by
  have hmatrix : matrix = 1 := by
    apply Units.ext
    ext index
    exact index.elim0
  have hdet : Matrix.GeneralLinearGroup.det matrix = 1 := by
    rw [hmatrix]
    exact map_one Matrix.GeneralLinearGroup.det
  exact (mem_elementarySubgroup_iff_det_eq_one_of_stableRangeCondition_one
    stable matrix).2 hdet

private theorem rank_one_determinant_one_is_identity
    (stable : Bass.StableRangeCondition R 1) (matrix : GL (Fin 1) R)
    (hdet : Matrix.GeneralLinearGroup.det matrix = 1) : matrix = 1 := by
  have hmem := (mem_elementarySubgroup_iff_det_eq_one_of_stableRangeCondition_one
    stable matrix).2 hdet
  rw [elementarySubgroup_eq_bot_of_subsingleton] at hmem
  exact Subgroup.mem_bot.mp hmem

private theorem zero_ring_generation (rank : ℕ)
    (matrix : GL (Fin rank) (ZMod 1)) :
    matrix ∈ elementarySubgroup (Fin rank) (ZMod 1) := by
  have stable : Bass.StableRangeCondition (ZMod 1) 1 := by
    intro distinguished remaining _
    refine ⟨fun _ => 0, fun _ => 0, ?_⟩
    exact Subsingleton.elim _ _
  have hdet : Matrix.GeneralLinearGroup.det matrix = 1 := Subsingleton.elim _ _
  exact (mem_elementarySubgroup_iff_det_eq_one_of_stableRangeCondition_one
    stable matrix).2 hdet

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

private theorem productMatrix_elementary_nonlocal :
    productMatrix ∈ elementarySubgroup (Fin 2) Coefficients ∧
    ¬ IsLocalRing Coefficients ∧
    ¬ IsUnit ((productMatrix : Matrix (Fin 2) (Fin 2) Coefficients) 0 0) ∧
    ¬ IsUnit ((productMatrix : Matrix (Fin 2) (Fin 2) Coefficients) 1 0) := by
  exact ⟨(mem_elementarySubgroup_iff_det_eq_one_of_stableRangeCondition_one
    product_condition productMatrix).2 productMatrix_det,
    nonlocal, productMatrix_first_column_nonunit.1, productMatrix_first_column_nonunit.2⟩

private theorem productMatrix_class_one :
    QuotientGroup.mk' (stableElementarySubgroup Coefficients)
      (StableGL.stage Coefficients 2 productMatrix) = 1 := by
  apply (StableGL.quotientDet_injective_of_stableRangeCondition_one product_condition)
  simp only [StableGL.quotientDet_mk, StableGL.det_stage, productMatrix_det,
    map_one]

private theorem productMatrix_bool_index :
    let indexEquiv := finTwoEquiv
    reindexEquiv Coefficients indexEquiv productMatrix ∈
      elementarySubgroup Bool Coefficients := by
  intro indexEquiv
  have hdet : Matrix.GeneralLinearGroup.det
      (reindexEquiv Coefficients indexEquiv productMatrix) = 1 := by
    apply Units.ext
    change (Matrix.reindex indexEquiv indexEquiv
      (productMatrix : Matrix (Fin 2) (Fin 2) Coefficients)).det = 1
    rw [Matrix.det_reindex_self]
    exact congrArg Units.val productMatrix_det
  exact (mem_elementarySubgroup_iff_det_eq_one_of_stableRangeCondition_one
    product_condition (reindexEquiv Coefficients indexEquiv productMatrix)).2 hdet

private theorem productMatrix_coefficient_map :
    let projection := RingHom.fst (ZMod 2) (ZMod 2)
    StableGL.quotientDetMulEquivOfStableRangeConditionOne
      Bass.stableRangeCondition_one_of_isLocalRing
      (QuotientGroup.map (stableElementarySubgroup Coefficients)
        (stableElementarySubgroup (ZMod 2)) (StableGL.map projection)
        ((Subgroup.map_le_iff_le_comap).mp (StableGL.map_elementarySubgroup_le projection))
        (StableGL.quotientRankOneUnits Coefficients 1)) = 1 := by
  intro projection
  rw [StableGL.quotientDetMulEquivOfStableRangeConditionOne_map product_condition
    Bass.stableRangeCondition_one_of_isLocalRing]
  simp

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

section NontrivialUnits

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private def nontrivialUnit : (ZMod 3)ˣ := ⟨2, 2, by decide, by decide⟩

private theorem nontrivialUnit_ne_one : nontrivialUnit ≠ 1 := by decide

private theorem nontrivial_finite_rank_one_not_elementary :
    scalar (Fin 1) nontrivialUnit ∉ elementarySubgroup (Fin 1) (ZMod 3) := by
  rw [mem_elementarySubgroup_iff_det_eq_one_of_stableRangeCondition_one
    (Bass.stableRangeCondition_one_of_isLocalRing (R := ZMod 3))]
  simpa only [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one] using
    nontrivialUnit_ne_one

private theorem nontrivial_rank_one_determinant :
    StableGL.quotientDetMulEquivOfStableRangeConditionOne
      (Bass.stableRangeCondition_one_of_isLocalRing (R := ZMod 3))
      (StableGL.quotientRankOneUnits (ZMod 3) nontrivialUnit) = nontrivialUnit ∧
    (StableGL.quotientDetMulEquivOfStableRangeConditionOne
      (Bass.stableRangeCondition_one_of_isLocalRing (R := ZMod 3))).symm
      nontrivialUnit = StableGL.quotientRankOneUnits (ZMod 3) nontrivialUnit ∧
    StableGL.quotientRankOneUnits (ZMod 3) nontrivialUnit ≠ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [StableGL.quotientDetMulEquivOfStableRangeConditionOne_apply,
      StableGL.quotientDet_quotientRankOneUnits]
  · exact StableGL.quotientDetMulEquivOfStableRangeConditionOne_symm_apply _ _
  · intro equality
    have hdet := congrArg (StableGL.quotientDet (ZMod 3)) equality
    exact nontrivialUnit_ne_one (by
      simpa only [StableGL.quotientDet_quotientRankOneUnits, map_one] using hdet)

private theorem nontrivial_rank_one_not_elementary :
    StableGL.rankOneUnits (ZMod 3) nontrivialUnit ∉
      stableElementarySubgroup (ZMod 3) := by
  rw [StableGL.elementary_eq_ker_det_of_stableRangeCondition_one
    (Bass.stableRangeCondition_one_of_isLocalRing (R := ZMod 3))]
  simpa only [MonoidHom.mem_ker, StableGL.det_rankOneUnits] using nontrivialUnit_ne_one

end NontrivialUnits

end StableRangeTests.ElementaryGenerationClient
