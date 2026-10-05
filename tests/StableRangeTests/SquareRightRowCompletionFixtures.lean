/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.RightRowCompletion
public import StableRangeTests.RightRowCompletionFixtures
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Noetherian.Orzech
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber

/-!
# Invariant-basis-number row fixtures

The integer unary row and the noncommutative two-by-two integer-matrix row
have genuinely free right coefficient kernels. The empty row cannot be
right-unimodular over an IBN ring. The matrix-ring IBN instance follows from
Mathlib's Noetherian matrix-ring instance and Orzech's theorem.
-/

set_option warningAsError true

@[expose] public section

namespace SquareRightRowCompletionFixtures

open scoped Matrix
open RightRowCompletionFixtures

/-- A matrix ring over the integers satisfies IBN, without commutativity of
the matrix coefficients. -/
theorem matrix_ibn : InvariantBasisNumber Coeff := by infer_instance

theorem integer_unary_kernel_free :
    Module.Free ℤᵐᵒᵖ
      (LinearMap.ker (dotProductBilin ℤ ℤᵐᵒᵖ (![1] : Fin 1 → ℤ))) := by
  have hrow : (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 = (![1] : Fin 1 → ℤ) := by
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simp
  exact (Matrix.isRightUnimodular_and_free_kernel_iff_exists_rectangular_inverse
    ℤ (![1] : Fin 1 → ℤ)).mpr
      ⟨0, 1, 1, hrow, by simp, by simp⟩ |>.2

/-- The original matrix-ring row has a nonzero but free coefficient kernel. -/
theorem matrix_kernel_free :
    Module.Free Coeffᵐᵒᵖ
      (LinearMap.ker (dotProductBilin Coeff Coeffᵐᵒᵖ row)) := by
  have : Module.Free Coeffᵐᵒᵖ Coeff :=
    Module.Free.of_equiv (MulOpposite.opLinearEquiv Coeffᵐᵒᵖ (M := Coeff)).symm
  exact Module.Free.of_equiv kernelCoordinates.symm

/-- The zero-length coefficient row cannot be right-unimodular over an IBN
ring, since IBN rules out the zero ring. -/
theorem empty_not_rightUnimodular (R : Type*) [Ring R] [InvariantBasisNumber R] :
    ¬ Bass.IsRightUnimodular (Fin.elim0 : Fin 0 → R) := by
  have : Nontrivial R := nontrivial_of_invariantBasisNumber R
  rintro ⟨b, hb⟩
  simp at hb

end SquareRightRowCompletionFixtures
