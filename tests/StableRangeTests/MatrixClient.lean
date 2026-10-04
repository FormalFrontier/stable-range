/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange
public import StableRangeTests.MatrixFixtures
import StableRangeTests.PublicAPIClient
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Finite-matrix stable-range clients

These clients instantiate finite matrix preservation over a nonreduced ring,
an infinite product of nonreduced rings, the zero ring, and a formal power-series
ring. The two-by-two example has a right-unimodular pair of nonunits; its
explicit correction is checked without using the matrix preservation theorem.
-/

set_option warningAsError true

@[expose] public section

namespace StableRangeTests.MatrixClient

universe u

open StableRangeTests.MatrixFixtures

private theorem zmodFour_condition : Bass.StableRangeCondition (ZMod 4) 1 :=
  Bass.stableRangeCondition_one_of_krullDimLE_zero

private theorem infiniteProduct_condition : Bass.StableRangeCondition (ℕ → ZMod 4) 1 :=
  Bass.stableRangeCondition_pi (fun _ : ℕ => zmodFour_condition)

private theorem zeroRing_condition : Bass.StableRangeCondition (ZMod 1) 1 :=
  Bass.stableRangeCondition_mono (Nat.zero_le 1)
    StableRangePublicAPIClient.zero_ring_condition

private theorem finite_matrix_condition {ι : Type u} [Fintype ι] [DecidableEq ι] :
    Bass.StableRangeCondition (Matrix ι ι (ZMod 4)) 1 :=
  Bass.stableRangeCondition_one_matrix zmodFour_condition

example : Bass.StableRangeCondition (Matrix (Fin 0) (Fin 0) (ZMod 4)) 1 :=
  finite_matrix_condition

example : Bass.StableRangeCondition (Matrix (Fin 1) (Fin 1) (ZMod 4)) 1 :=
  finite_matrix_condition

example : Bass.StableRangeCondition (Matrix (Fin 2) (Fin 2) (ZMod 4)) 1 :=
  finite_matrix_condition

example : Bass.StableRangeCondition (Matrix (Fin 2) (Fin 2) (ℕ → ZMod 4)) 1 :=
  Bass.stableRangeCondition_one_matrix infiniteProduct_condition

private theorem infiniteProduct_matrix_two_ne_zero :
    (2 : Matrix (Fin 2) (Fin 2) (ℕ → ZMod 4)) ≠ 0 := by
  intro hzero
  have hentry : (2 : ZMod 4) = 0 := by
    simpa [Matrix.ofNat_apply, Pi.ofNat_apply] using
      congrFun (congrArg
        (fun matrix : Matrix (Fin 2) (Fin 2) (ℕ → ZMod 4) => matrix 0 0) hzero) 0
  exact (show (2 : ZMod 4) ≠ 0 from by decide) hentry

private theorem infiniteProduct_matrix_two_sq_zero :
    (2 : Matrix (Fin 2) (Fin 2) (ℕ → ZMod 4)) * 2 = 0 := by
  have hcoeff : (2 : ℕ → ZMod 4) * 2 = 0 := by
    funext index
    change (2 : ZMod 4) * 2 = 0
    decide
  calc
    (2 : Matrix (Fin 2) (Fin 2) (ℕ → ZMod 4)) * 2 =
        Matrix.diagonal (fun _ : Fin 2 => (2 : ℕ → ZMod 4) * 2) := by
      simpa only [Matrix.diagonal_ofNat] using
        (Matrix.diagonal_mul_diagonal
          (fun _ : Fin 2 => (2 : ℕ → ZMod 4))
          (fun _ : Fin 2 => (2 : ℕ → ZMod 4)))
    _ = 0 := by simp only [hcoeff, Matrix.diagonal_zero]

private theorem infiniteProduct_matrix_two_mul_self (matrix :
    Matrix (Fin 2) (Fin 2) (ℕ → ZMod 4)) :
    (2 : Matrix (Fin 2) (Fin 2) (ℕ → ZMod 4)) * matrix * 2 = 0 := by
  have hcomm : (2 : Matrix (Fin 2) (Fin 2) (ℕ → ZMod 4)) * matrix = matrix * 2 := by
    simp only [two_mul, mul_two]
  calc
    (2 : Matrix (Fin 2) (Fin 2) (ℕ → ZMod 4)) * matrix * 2 =
        matrix * (2 * 2) := by rw [hcomm, mul_assoc]
    _ = 0 := by rw [infiniteProduct_matrix_two_sq_zero, mul_zero]

example : ∃ element : Matrix (Fin 2) (Fin 2) (ℕ → ZMod 4),
    element ≠ 0 ∧ ∀ matrix, element * matrix * element = 0 :=
  ⟨2, infiniteProduct_matrix_two_ne_zero, infiniteProduct_matrix_two_mul_self⟩

example : Bass.StableRangeCondition (Matrix Bool Bool (ZMod 4)) 1 :=
  (finite_matrix_condition (ι := Fin (Fintype.card Bool))).map_equiv
    (Matrix.reindexRingEquiv (ZMod 4) (Fintype.equivFin Bool).symm)

example : Bass.StableRangeCondition (Matrix (Fin 2) (Fin 2) (ZMod 1)) 1 :=
  Bass.stableRangeCondition_one_matrix zeroRing_condition

private theorem zeroRing_all_units (matrix : Matrix (Fin 2) (Fin 2) (ZMod 1)) :
    IsUnit matrix := by
  have hmatrix : matrix = 1 := Subsingleton.elim _ _
  rw [hmatrix]
  exact isUnit_one

private theorem powerSeries_condition :
    Bass.StableRangeCondition (PowerSeries ℚ) 1 :=
  Bass.stableRangeCondition_one_of_isLocalRing

example : Bass.StableRangeCondition (Matrix (Fin 2) (Fin 2) (PowerSeries ℚ)) 1 :=
  Bass.stableRangeCondition_one_matrix powerSeries_condition

private theorem projections_correctable :
    ∃ correction : Matrix (Fin 2) (Fin 2) (ZMod 4),
      IsUnit (secondProjection - firstProjection * correction) :=
  (Bass.stableRangeCondition_one_iff_forall_isUnit_sub_mul.mp
    (Bass.stableRangeCondition_one_matrix zmodFour_condition))
      firstProjection secondProjection
      ⟨firstProjection, secondProjection, projections_right_witness (R := ZMod 4)⟩

/-- A right-unimodular pair of nonunits in a nonzero two-by-two matrix ring. -/
theorem nonunit_pair_correctable :
    ∃ first second firstWitness secondWitness : Matrix (Fin 2) (Fin 2) (ZMod 4),
      ¬ IsUnit first ∧ ¬ IsUnit second ∧
        first * firstWitness + second * secondWitness = 1 ∧
        ∃ correction : Matrix (Fin 2) (Fin 2) (ZMod 4),
          IsUnit (second - first * correction) := by
  have hnontrivial : Nontrivial (ZMod 4) := ⟨⟨0, 1, by decide⟩⟩
  exact ⟨firstProjection, secondProjection, firstProjection, secondProjection,
    @firstProjection_nonunit (ZMod 4) _ hnontrivial,
    @secondProjection_nonunit (ZMod 4) _ hnontrivial,
    projections_right_witness, projections_correctable⟩

example : IsUnit ((secondProjection : Matrix (Fin 2) (Fin 2) (ZMod 4)) -
    firstProjection * (-1 : Matrix (Fin 2) (Fin 2) (ZMod 4))) := by
  rw [projections_shortening (R := ZMod 4)]
  exact isUnit_one

end StableRangeTests.MatrixClient
