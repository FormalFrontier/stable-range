/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange
import StableRangeTests.PublicAPIClient
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Noncommutative stable-range clients

Complementary projections in a two-by-two matrix ring give a right-unimodular
pair of nonunits that shortens explicitly. Infinite and empty products and a
formal-power-series radical quotient exercise the public stable-range API.
-/

set_option warningAsError true

@[expose] public section

namespace StableRangeTests.SemisimpleClient

universe u v w

variable {D : Type u} [DivisionRing D]

private def firstProjection : Matrix (Fin 2) (Fin 2) D := !![1, 0; 0, 0]
private def secondProjection : Matrix (Fin 2) (Fin 2) D := !![0, 0; 0, 1]
private def upperMatrixUnit : Matrix (Fin 2) (Fin 2) D := !![0, 1; 0, 0]
private def lowerMatrixUnit : Matrix (Fin 2) (Fin 2) D := !![0, 0; 1, 0]

private theorem projections_sum :
    (firstProjection : Matrix (Fin 2) (Fin 2) D) + secondProjection = 1 := by
  ext row column; fin_cases row <;> fin_cases column <;>
    simp [firstProjection, secondProjection, Matrix.of_apply]

private theorem firstProjection_idempotent :
    (firstProjection : Matrix (Fin 2) (Fin 2) D) * firstProjection = firstProjection := by
  ext row column; fin_cases row <;> fin_cases column <;>
    simp [firstProjection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]

private theorem secondProjection_idempotent :
    (secondProjection : Matrix (Fin 2) (Fin 2) D) * secondProjection = secondProjection := by
  ext row column; fin_cases row <;> fin_cases column <;>
    simp [secondProjection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]

private theorem firstProjection_nonunit :
    ¬ IsUnit (firstProjection : Matrix (Fin 2) (Fin 2) D) := by
  intro h
  obtain ⟨inverse, hright, _⟩ := isUnit_iff_exists.mp h
  have hentry := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) D => matrix 1 1) hright
  simp [firstProjection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply] at hentry

private theorem secondProjection_nonunit :
    ¬ IsUnit (secondProjection : Matrix (Fin 2) (Fin 2) D) := by
  intro h
  obtain ⟨inverse, hright, _⟩ := isUnit_iff_exists.mp h
  have hentry := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) D => matrix 0 0) hright
  simp [secondProjection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply] at hentry

private theorem projections_unimodular :
    Bass.IsRightUnimodularCons (firstProjection : Matrix (Fin 2) (Fin 2) D)
      (fun _ : Fin 1 => secondProjection) := by
  refine ⟨firstProjection, fun _ => secondProjection, ?_⟩
  simpa only [Fin.sum_univ_one, firstProjection_idempotent,
    secondProjection_idempotent] using (projections_sum (D := D))

private theorem projections_shorten :
    (secondProjection : Matrix (Fin 2) (Fin 2) D) -
      firstProjection * (-1 : Matrix (Fin 2) (Fin 2) D) = 1 := by
  calc
    secondProjection - firstProjection * (-1 : Matrix (Fin 2) (Fin 2) D) =
        secondProjection + firstProjection := by
      simp
    _ = firstProjection + secondProjection := add_comm _ _
    _ = 1 := projections_sum

private theorem projections_shortening_witness :
    Bass.IsRightUnimodular
      (fun _ : Fin 1 => (secondProjection : Matrix (Fin 2) (Fin 2) D) -
        firstProjection * (-1 : Matrix (Fin 2) (Fin 2) D)) := by
  refine ⟨fun _ => 1, ?_⟩
  simpa only [Fin.sum_univ_one, mul_one] using (projections_shorten (D := D))

private theorem matrix_units_do_not_commute :
    (upperMatrixUnit : Matrix (Fin 2) (Fin 2) D) * lowerMatrixUnit ≠
      lowerMatrixUnit * upperMatrixUnit := by
  intro h
  have hentry := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) D => matrix 0 0) h
  simp [upperMatrixUnit, lowerMatrixUnit, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.of_apply] at hentry

/-- The two off-diagonal matrix units do not commute over a division ring. -/
theorem matrix_units_noncommutative :
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) D) *
      (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) D) ≠
    (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) D) *
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) D) := by
  simpa only [upperMatrixUnit, lowerMatrixUnit] using
    (matrix_units_do_not_commute (D := D))

private theorem semisimple_matrix_condition :
    Bass.StableRangeCondition (Matrix (Fin 2) (Fin 2) D) 1 :=
  Bass.stableRangeCondition_one_of_isSemisimpleRing

private theorem semisimple_matrix_shortens_nonunits :
    ¬ IsUnit (firstProjection : Matrix (Fin 2) (Fin 2) D) ∧
    ¬ IsUnit (secondProjection : Matrix (Fin 2) (Fin 2) D) ∧
    ∃ shortening witness : Matrix (Fin 2) (Fin 2) D,
      (secondProjection - firstProjection * shortening) * witness = 1 := by
  refine ⟨firstProjection_nonunit, secondProjection_nonunit, ?_⟩
  obtain ⟨shortening, witness, hwitness⟩ :=
    (semisimple_matrix_condition (D := D)) firstProjection
      (fun _ : Fin 1 => secondProjection) projections_unimodular
  exact ⟨shortening 0, witness 0, by
    simpa only [Bass.IsRightUnimodular, Fin.sum_univ_one] using hwitness⟩

private theorem nonzero_matrix_index_zero_fails :
    ¬ Bass.StableRangeCondition (Matrix (Fin 2) (Fin 2) D) 0 :=
  Bass.not_stableRangeCondition_zero

private theorem infinite_matrix_product_condition :
    Bass.StableRangeCondition (ℕ → Matrix (Fin 2) (Fin 2) D) 1 :=
  Bass.stableRangeCondition_pi (fun _ =>
    Bass.IsUnitRegular.stableRangeCondition_one
      (Bass.isUnitRegular_matrix (K := D) (n := Fin 2)))

private theorem infinite_product_shorten :
    ∃ shortening : Fin 1 → (ℕ → Matrix (Fin 2) (Fin 2) D),
      Bass.IsRightUnimodular (fun index : Fin 1 =>
        (fun _ : ℕ => (secondProjection : Matrix (Fin 2) (Fin 2) D)) -
          (fun _ : ℕ => firstProjection) * shortening index) := by
  apply (infinite_matrix_product_condition (D := D))
    (fun _ => firstProjection) (fun _ : Fin 1 => fun _ => secondProjection)
  refine ⟨fun _ => firstProjection, fun _ : Fin 1 => fun _ => secondProjection, ?_⟩
  funext index
  simpa only [Fin.sum_univ_one, Pi.add_apply, Pi.mul_apply, Pi.one_apply,
    firstProjection_idempotent, secondProjection_idempotent] using
    (projections_sum (D := D))

private theorem empty_product_index_zero :
    Bass.StableRangeCondition (∀ _ : Empty, ℤ) 0 :=
  Bass.stableRangeCondition_pi (S := fun _ : Empty => ℤ) (n := 0)
    (fun index => index.elim)

private theorem zero_ring_index_zero : Bass.StableRangeCondition (ZMod 1) 0 :=
  StableRangePublicAPIClient.zero_ring_condition

private theorem infinite_zero_ring_product_index_zero :
    Bass.StableRangeCondition (ℕ → ZMod 1) 0 :=
  Bass.stableRangeCondition_pi (fun _ => zero_ring_index_zero)

private theorem zero_ring_index_one : Bass.StableRangeCondition (ZMod 1) 1 :=
  Bass.stableRangeCondition_one_of_isSemisimpleRing

section PowerSeries

variable {k : Type u} [Field k]

private theorem powerSeries_jacobson_isMaximal :
    (Ring.jacobson (PowerSeries k)).IsMaximal := by
  rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
  infer_instance

private theorem powerSeries_quotient_semisimple :
    IsSemisimpleRing (PowerSeries k ⧸ Ring.jacobson (PowerSeries k)) := by
  let _ := powerSeries_jacobson_isMaximal (k := k)
  let _ := Ideal.Quotient.field (Ring.jacobson (PowerSeries k))
  infer_instance

private theorem powerSeries_stableRangeCondition_one :
    Bass.StableRangeCondition (PowerSeries k) 1 := by
  let _ := powerSeries_quotient_semisimple (k := k)
  exact Bass.stableRangeCondition_one_of_isSemisimpleRing_quotient_jacobson

private theorem powerSeries_X_mem_jacobson :
    (PowerSeries.X : PowerSeries k) ∈ Ring.jacobson (PowerSeries k) := by
  rw [IsLocalRing.ringJacobson_eq_maximalIdeal, IsLocalRing.mem_maximalIdeal]
  change ¬ IsUnit (PowerSeries.X : PowerSeries k)
  simp [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]

private theorem powerSeries_jacobson_not_nilpotent :
    ¬ IsNilpotent (Ring.jacobson (PowerSeries k)) := by
  rintro ⟨index, hzero⟩
  have hX : (PowerSeries.X : PowerSeries k) ^ index = 0 := by
    have hmem := Ideal.pow_mem_pow (powerSeries_X_mem_jacobson (k := k)) index
    simp [hzero] at hmem
  have hcoeff := congrArg (PowerSeries.coeff index) hX
  simp at hcoeff

end PowerSeries

section Cancellation

variable {R : Type u} [Ring R] [IsSemisimpleRing R]
variable {A : Type v} {B : Type w}
variable [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

private theorem cancel_regular_summand
    (equivalence : (R × A) ≃ₗ[R] (R × B)) : Nonempty (A ≃ₗ[R] B) := by
  have condition : Bass.StableRangeCondition (Module.End R R) 1 :=
    (Bass.stableRangeCondition_one_of_isSemisimpleRing (R := Rᵐᵒᵖ)).map_equiv
      (RingEquiv.moduleEndSelf R)
  exact Bass.exists_linearEquiv_of_prod_of_end_stableRangeCondition_one condition equivalence

end Cancellation

end StableRangeTests.SemisimpleClient
