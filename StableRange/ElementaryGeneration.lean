/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.CommutativeStableRange
public import GeneralLinearGroups.UnitPivotInduction

/-!
# Elementary diagonalization under stable range one

For a commutative ring of Bass stable range one, elementary left multiplication
can create a unit leading entry in any invertible successor-rank matrix.
Two-sided elementary multiplication then reduces any invertible finite matrix
to a diagonal of units. The finite-index statement includes empty index types.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter I, §1 (Bass's stable-range condition and unimodular rows).
* `general-linear-groups`, `UnitPivotInduction` and
  `UnitPivotDiagonalization` (the existing conditional pivot induction,
  elementary factors and finite reindexing followed here).
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {R : Type u} [CommRing R]

/-- Bass stable range one supplies an elementary left factor making the
leading entry of an invertible matrix a unit. The factor uses the rectangular
upper shear formalized in `general-linear-groups`' `RectangularBlockUnits`. -/
theorem exists_elementary_unit_pivot_of_stableRangeCondition_one
    (stable : Bass.StableRangeCondition R 1) {rank : ℕ}
    (matrix : GL (Fin (rank + 1)) R) :
    ∃ factor : elementarySubgroup (Fin (rank + 1)) R,
      IsUnit (((((factor : GL (Fin (rank + 1)) R) * matrix) :
        GL (Fin (rank + 1)) R) : Matrix (Fin (rank + 1)) (Fin (rank + 1)) R) 0 0) := by
  let M : Matrix (Fin (rank + 1)) (Fin (rank + 1)) R := matrix
  let inverse : Matrix (Fin (rank + 1)) (Fin (rank + 1)) R :=
    (matrix⁻¹ : GL (Fin (rank + 1)) R)
  let tail : R := ∑ index : Fin rank, inverse 0 index.succ * M index.succ 0
  have hsum : (∑ row : Fin (rank + 1), inverse 0 row * M row 0) = 1 := by
    have h := congrArg
      (fun x : GL (Fin (rank + 1)) R =>
        ((x : Matrix (Fin (rank + 1)) (Fin (rank + 1)) R) 0 0))
      (inv_mul_cancel matrix)
    simpa only [Units.val_mul, Units.val_one, Matrix.mul_apply,
      Matrix.one_apply_eq, M, inverse] using h
  have hcons : Bass.IsRightUnimodularCons tail (fun _ : Fin 1 => M 0 0) := by
    refine ⟨1, fun _ => inverse 0 0, ?_⟩
    have hsplit : inverse 0 0 * M 0 0 + tail = 1 := by
      simpa only [Fin.sum_univ_succ, tail] using hsum
    simpa only [Fin.sum_univ_one, mul_one, one_mul, add_comm, mul_comm] using hsplit
  obtain ⟨coefficients, hrow⟩ := stable tail (fun _ : Fin 1 => M 0 0) hcons
  obtain ⟨witness, hwitness⟩ := hrow
  have hunit : IsUnit (M 0 0 - tail * coefficients 0) :=
    Bass.isUnit_of_mul_eq_one_of_stableRangeCondition_one stable
      (by simpa only [Fin.sum_univ_one] using hwitness)
  let shear : Matrix (Fin 1) (Fin rank) R :=
    fun _ index => -(coefficients 0 * inverse 0 index.succ)
  let factor : elementarySubgroup (Fin (rank + 1)) R :=
    reindexElementarySubgroup (Matrix.firstRestEquiv rank).symm
      ⟨rectangularUpperUnit shear, rectangularUpperUnit_mem_elementarySubgroup shear⟩
  refine ⟨factor, ?_⟩
  have hpivot :
      (((factor : GL (Fin (rank + 1)) R) * matrix : GL (Fin (rank + 1)) R) :
        Matrix (Fin (rank + 1)) (Fin (rank + 1)) R) 0 0 =
        M 0 0 - tail * coefficients 0 := by
    change (((reindexEquiv R (Matrix.firstRestEquiv rank).symm
      (rectangularUpperUnit shear) : GL (Fin (rank + 1)) R) * matrix :
      GL (Fin (rank + 1)) R) : Matrix (Fin (rank + 1)) (Fin (rank + 1)) R) 0 0 = _
    rw [Units.val_mul, reindexed_rectangularUpperUnit_mul_apply_zero]
    change M 0 0 + ∑ index : Fin rank,
      -(coefficients 0 * inverse 0 index.succ) * M index.succ 0 = _
    simp only [neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg, mul_assoc]
    rw [← Finset.mul_sum]
    dsimp only [tail]
    rw [mul_comm (coefficients 0)]
  rw [hpivot]
  exact hunit

/-- A commutative stable-range-one ring admits elementary two-sided
diagonalization of every invertible matrix, including the empty matrix.
Uses the conditional pivot induction in `general-linear-groups`' `UnitPivotInduction`. -/
theorem exists_elementary_diagonalization_of_stableRangeCondition_one
    (stable : Bass.StableRangeCondition R 1) {rank : ℕ} (matrix : GL (Fin rank) R) :
    ∃ (left right : elementarySubgroup (Fin rank) R) (diagonal : Fin rank → Rˣ),
      (left : GL (Fin rank) R) * matrix * (right : GL (Fin rank) R) =
        diagonalUnit diagonal := by
  exact exists_elementary_diagonalization_of_unit_pivots
    (fun _ matrix => exists_elementary_unit_pivot_of_stableRangeCondition_one stable matrix)
    matrix

/-- The elementary diagonalization is invariant under finite reindexing;
no chosen ordering of the index type is needed by clients. -/
theorem exists_elementary_diagonalization_finite_of_stableRangeCondition_one
    (stable : Bass.StableRangeCondition R 1) {ι : Type v}
    [Fintype ι] [DecidableEq ι] (matrix : GL ι R) :
    ∃ (left right : elementarySubgroup ι R) (diagonal : ι → Rˣ),
      (left : GL ι R) * matrix * (right : GL ι R) = diagonalUnit diagonal := by
  let equiv := Fintype.equivFin ι
  obtain ⟨left, right, diagonal, hdiag⟩ :=
    exists_elementary_diagonalization_of_stableRangeCondition_one stable
      (reindexEquiv R equiv matrix)
  refine ⟨reindexElementarySubgroup equiv.symm left,
    reindexElementarySubgroup equiv.symm right, diagonal ∘ equiv, ?_⟩
  have htransport := congrArg (reindexEquiv R equiv.symm) hdiag
  have hreindex : reindexEquiv R equiv.symm (diagonalUnit diagonal) =
      diagonalUnit (diagonal ∘ equiv) := by
    apply Units.ext
    ext row column
    simp [reindexEquiv_apply, Matrix.diagonal_apply, equiv.injective.eq_iff]
  have hcancel : reindexEquiv R equiv.symm (reindexEquiv R equiv matrix) = matrix := by
    change (reindexEquiv R equiv).symm ((reindexEquiv R equiv) matrix) = matrix
    exact MulEquiv.symm_apply_apply _ _
  simpa only [reindexElementarySubgroup_coe, map_mul, hcancel, hreindex] using htransport

end Matrix.GeneralLinearGroup
