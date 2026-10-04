/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange
public import StableRangeTests.MatrixFixtures
import StableRangeTests.SemisimpleClient
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Nonempty finite-matrix stable-range clients

Semisimplicity supplies the outer matrix condition independently. The
nonempty-index reflection statement then yields a two-sided unit witness for a
right-handed shortening over noncommutative coefficients. Trivial coefficients
exercise the coefficient hypothesis without nontriviality.
-/

set_option warningAsError true

@[expose] public section

namespace StableRangeTests.MatrixReflectionClient

universe u

open StableRangeTests.MatrixFixtures

private theorem nested_semisimple_condition {D : Type u} [DivisionRing D] :
    Bass.StableRangeCondition
      (Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) D)) 1 :=
  Bass.stableRangeCondition_one_of_isSemisimpleRing

/-- Noncommuting matrix coefficients with nonunit projections admit a right-handed
shortening to a two-sided unit under nonempty finite-matrix reflection. -/
theorem noncommutative_coefficient_shortening {D : Type u} [DivisionRing D] :
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) D) * !![0, 0; 1, 0] ≠
      (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) D) * !![0, 1; 0, 0] ∧
    ¬ IsUnit (firstProjection : Matrix (Fin 2) (Fin 2) D) ∧
    ¬ IsUnit (secondProjection : Matrix (Fin 2) (Fin 2) D) ∧
    ∃ correction inverse : Matrix (Fin 2) (Fin 2) D,
      (secondProjection - firstProjection * correction) * inverse = 1 ∧
      inverse * (secondProjection - firstProjection * correction) = 1 := by
  refine ⟨StableRangeTests.SemisimpleClient.matrix_units_noncommutative,
    firstProjection_nonunit, secondProjection_nonunit, ?_⟩
  have hcoeff : Bass.StableRangeCondition (Matrix (Fin 2) (Fin 2) D) 1 :=
    (Bass.stableRangeCondition_one_matrix_iff (ι := Fin 3)).mp
      nested_semisimple_condition
  obtain ⟨correction, hunit⟩ :=
    (Bass.stableRangeCondition_one_iff_forall_isUnit_sub_mul.mp hcoeff)
      firstProjection secondProjection
      ⟨firstProjection, secondProjection, projections_right_witness⟩
  obtain ⟨inverse, hright, hleft⟩ := isUnit_iff_exists.mp hunit
  exact ⟨correction, inverse, hright, hleft⟩

example (first second : ZMod 1) :
    ∃ correction : ZMod 1, IsUnit (second - first * correction) := by
  have houter : Bass.StableRangeCondition (Matrix (Fin 3) (Fin 3) (ZMod 1)) 1 :=
    Bass.stableRangeCondition_one_of_isSemisimpleRing
  have hcoeff : Bass.StableRangeCondition (ZMod 1) 1 :=
    (Bass.stableRangeCondition_one_matrix_iff (ι := Fin 3)).mp houter
  exact (Bass.stableRangeCondition_one_iff_forall_isUnit_sub_mul.mp hcoeff) first second
    ⟨0, 0, Subsingleton.elim _ _⟩

end StableRangeTests.MatrixReflectionClient
