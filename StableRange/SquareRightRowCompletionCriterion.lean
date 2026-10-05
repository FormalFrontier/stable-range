/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.SquareRightRowCompletion

/-!
# Free right-kernel criterion for square completion

Over an arbitrary ring with invariant basis number, freeness of the right
coefficient kernel of a right-unimodular successor-length row is equivalent
to completion as a square matrix unit. The explicit construction remembers
the original section column as a column of the inverse. The converse does
not need invariant basis number.

This does not assert dimension-unspecified completion for non-IBN rings.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  I.1.2.1 (free-kernel/basis-extension idea).
* Mathlib, `LinearAlgebra.Matrix.InvariantBasisNumber` (dimension of a
  two-sided invertible rectangular matrix).
* `StableRange.SquareRightRowCompletion` (unit construction, actions and
  reverse free-kernel implication).
-/

set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace Matrix

universe u

/-- The specified right-unimodular row has a free right coefficient kernel
if and only if it extends to a square unit retaining the specified inverse
column. This is the free-kernel/basis-extension idea of Weibel, *The K-book*,
I.1.2.1, with IBN recovering the number of coordinates; it makes no assertion
about dimension-unspecified completion over rings without IBN. -/
theorem free_rightCoefficientKernel_iff_exists_gl (R : Type u)
    [Ring R] [InvariantBasisNumber R] {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1) :
    Module.Free Rᵐᵒᵖ (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a)) ↔
      ∃ g : GeneralLinearGroup (Fin (m + 1)) R,
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) 0 = a ∧
          (fun i ↦ (g⁻¹).val i 0) = b := by
  constructor
  · intro hfree
    exact ⟨rightRowCompletionGLOfFree R a b hb hfree,
      rightRowCompletionGLOfFree_zero R a b hb hfree,
      rightRowCompletionGLOfFree_inv_zero R a b hb hfree⟩
  · rintro ⟨g, hrow, _⟩
    exact free_rightCoefficientKernel_of_gl R a g hrow

/-- A successor-length row is right-unimodular with a free right coefficient
kernel exactly when it is a row of an invertible square matrix. As in Weibel,
*The K-book*, I.1.2.1, the basis-extension direction uses IBN only to fix the
size of the matrix; the reverse direction does not use IBN. -/
theorem isRightUnimodular_and_free_kernel_iff_exists_gl (R : Type u)
    [Ring R] [InvariantBasisNumber R] {m : ℕ} (a : Fin (m + 1) → R) :
    (Bass.IsRightUnimodular a ∧
      Module.Free Rᵐᵒᵖ (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a))) ↔
        ∃ g : GeneralLinearGroup (Fin (m + 1)) R,
          (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) 0 = a := by
  constructor
  · rintro ⟨⟨b, hb⟩, hfree⟩
    obtain ⟨g, hrow, _⟩ :=
      (free_rightCoefficientKernel_iff_exists_gl R a b hb).mp hfree
    exact ⟨g, hrow⟩
  · rintro ⟨g, hrow⟩
    exact ⟨isRightUnimodular_of_rectangular_inverse R a g.val g.inv
      hrow g.val_inv, free_rightCoefficientKernel_of_gl R a g hrow⟩

end Matrix
