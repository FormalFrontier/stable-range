/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.CountableEndomorphism

/-!
# A concrete rational endomorphism-ring client

The even and odd maps act nontrivially on a finitely supported rational
sequence. The unary row has a genuinely free kernel, with coordinates
read from and inserted into the original right-coefficient column.
Invariant basis number also fails when the underlying module is zero.
-/

set_option warningAsError true

public section

open scoped Matrix
open CountableEndomorphism

namespace StableRangeTests

private abbrev Coeff := Module.End ℚ (ℕ →₀ ℚ)

/-- The parity equivalence reads even and odd rational singleton coordinates. -/
theorem parityEquiv_single_coordinates (evenValue oddValue : ℚ) :
    (parityEquiv ℚ ℚ (Finsupp.single 0 evenValue +
      Finsupp.single 1 oddValue)).1 0 = evenValue ∧
      (parityEquiv ℚ ℚ (Finsupp.single 0 evenValue +
        Finsupp.single 1 oddValue)).2 0 = oddValue := by
  constructor
  · simp
  · simp

example (evenValue oddValue : ℚ) :
    (parityEquiv ℚ ℚ).symm
        (Finsupp.single 0 evenValue, Finsupp.single 0 oddValue) 0 = evenValue ∧
      (parityEquiv ℚ ℚ).symm
        (Finsupp.single 0 evenValue, Finsupp.single 0 oddValue) 1 = oddValue := by
  constructor
  · simpa using parityEquiv_symm_apply_even ℚ ℚ
      (Finsupp.single 0 evenValue, Finsupp.single 0 oddValue) 0
  · simpa using parityEquiv_symm_apply_odd ℚ ℚ
      (Finsupp.single 0 evenValue, Finsupp.single 0 oddValue) 0

example (evenValue oddValue : ℚ) :
    x₀ ℚ ℚ (Finsupp.single 0 evenValue) 1 = 0 ∧
      x₁ ℚ ℚ (Finsupp.single 0 oddValue) 0 = 0 := by
  constructor
  · simpa using x₀_apply_odd ℚ ℚ (Finsupp.single 0 evenValue) 0
  · simpa using x₁_apply_even ℚ ℚ (Finsupp.single 0 oddValue) 0

example : Subsingleton (ℕ →₀ (Fin 0 → ℚ)) ∧
    ¬ InvariantBasisNumber (Module.End ℚ (ℕ →₀ (Fin 0 → ℚ))) :=
  ⟨inferInstance, not_invariantBasisNumber ℚ (Fin 0 → ℚ)⟩

example : x₁ ℚ ℚ (Finsupp.single 0 (1 : ℚ)) 1 = 1 := by
  simpa using x₁_apply_odd ℚ ℚ (Finsupp.single 0 (1 : ℚ)) 0

example : y₁ ℚ ℚ (x₁ ℚ ℚ (Finsupp.single 0 (1 : ℚ))) 0 = 1 := by
  rw [← Module.End.mul_apply, y₁_mul_x₁]
  simp

example : (rectangularRow ℚ ℚ * rectangularColumn ℚ ℚ) 1 1 = 1 := by
  rw [rectangularRow_mul_rectangularColumn]
  simp

example : Bass.IsRightUnimodular (row ℚ ℚ) ∧
    Module.Free Coeffᵐᵒᵖ
      (LinearMap.ker (dotProductBilin Coeff Coeffᵐᵒᵖ (row ℚ ℚ))) :=
  (Matrix.isRightUnimodular_and_free_kernel_iff_exists_rectangular_inverse
    Coeff (row ℚ ℚ)).mpr
    ⟨1, rectangularRow ℚ ℚ, rectangularColumn ℚ ℚ,
      rectangularRow_first ℚ ℚ, rectangularRow_mul_rectangularColumn ℚ ℚ,
      rectangularColumn_mul_rectangularRow ℚ ℚ⟩

example : y₁ ℚ ℚ *
    (((kernelEquiv ℚ ℚ).symm (fun _ : Fin 1 => (1 : Coeff))).1 0) = 1 := by
  rw [← kernelEquiv_apply_zero]
  simp

example :
    (((kernelEquiv ℚ ℚ).symm (fun _ : Fin 1 => (1 : Coeff))).1 0) = x₁ ℚ ℚ := by
  simpa using kernelEquiv_symm_apply_zero ℚ ℚ (1 : Coeff)

example (g : Matrix.GeneralLinearGroup (Fin 1) Coeff) :
    (g : Matrix (Fin 1) (Fin 1) Coeff) 0 ≠ row ℚ ℚ := by
  intro h
  exact (rightUnimodular_free_kernel_no_square ℚ ℚ).2.2.2 ⟨g, h⟩

example : ∃ k : LinearMap.ker
    (dotProductBilin Coeff Coeffᵐᵒᵖ (row ℚ ℚ)), k ≠ 0 :=
  (rightUnimodular_free_kernel_no_square ℚ ℚ).2.2.1

end StableRangeTests
