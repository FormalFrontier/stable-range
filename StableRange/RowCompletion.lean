/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.RowKernel
public import StableRange.BassDimension

/-!
# Completion of a unimodular coefficient row

A right-unimodular row of length `n + 1` over a ring satisfying `(S_s)` for
`s ≤ n` is the first row of an invertible square matrix. The completing
self-equivalence sends `x` to a vector with coordinate zero equal to `a ⬝ᵥ x`;
its matrix has first row `a`, with both inverse identities. The result includes
the zero ring.

## References

* C. Weibel, *The K-book* (2013), I.1.3, for stable-range row completion.
* Prism, exact-size stable-range cancellation and first-row assembly design,
  for the coordinate-first equivalence formulation.
* Formal Frontier, Stable Range, `StableRange.RowKernel`, for the explicit
  unimodular row-kernel equivalence and the kernel/product splitting.
* Mathlib, `Mathlib.LinearAlgebra.Matrix.ToLin`, for the matrix representation
  of linear maps on finite-coordinate modules.
-/

set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace LinearEquiv

universe u

/-- Complete a right-unimodular coefficient row to a self-equivalence of the
finite free module. Following the row-completion statement in Weibel,
*The K-book*, I.1.3, its first output coordinate is the original coefficient
functional, not merely a row equivalent to it. -/
noncomputable def coefficientRowCompletionOfStableRangeCondition
    (R : Type u) [CommRing R] (n : ℕ) (a : Fin (n + 1) → R)
    (ha : Bass.IsRightUnimodular a) {s : ℕ}
    (hs : Bass.StableRangeCondition R s) (hsn : s ≤ n) :
    (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R) := by
  let kerEquiv : LinearMap.ker (Bass.coefficientRowScalarMap R (n + 1) a) ≃ₗ[R]
      (Fin n → R) :=
    (LinearEquiv.ofEq _ _ (Bass.ker_coefficientRowScalarMap_eq R (n + 1) a)).trans
      (Bass.coefficientRowKernelEquivSuccOfStableRangeCondition R n
        (Bass.stableRangeCondition_mono hsn hs) a ha)
  exact (((Bass.kernelProdEquivOfIsRightUnimodular R (n + 1) a ha).symm.trans
    (LinearEquiv.prodComm R _ _)).trans
      ((LinearEquiv.refl R R).prodCongr kerEquiv)).trans
    (Fin.consLinearEquiv R (fun _ : Fin (n + 1) ↦ R))

/-- The first output coordinate of the completion is the input row applied
to the given vector. -/
@[simp]
theorem coefficientRowCompletionOfStableRangeCondition_apply_zero
    (R : Type u) [CommRing R] (n : ℕ) (a : Fin (n + 1) → R)
    (ha : Bass.IsRightUnimodular a) {s : ℕ}
    (hs : Bass.StableRangeCondition R s) (hsn : s ≤ n)
    (x : Fin (n + 1) → R) :
    coefficientRowCompletionOfStableRangeCondition R n a ha hs hsn x 0 = a ⬝ᵥ x := by
  simp [coefficientRowCompletionOfStableRangeCondition,
    Bass.kernelProdEquivOfIsRightUnimodular_symm_snd]

/-- A noetherian Krull-dimension upper bound yields the same coordinate-first
completion whenever the row length exceeds that bound by at least two. -/
noncomputable def coefficientRowCompletionOfKrullDimLE
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {d : ℕ} [Ring.KrullDimLE d R] (n : ℕ) (a : Fin (n + 1) → R)
    (ha : Bass.IsRightUnimodular a) (hdn : d + 1 ≤ n) :
    (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R) :=
  coefficientRowCompletionOfStableRangeCondition R n a ha
    (Bass.stableRangeCondition_succ_of_krullDimLE (R := R) (d := d)) hdn

@[simp]
theorem coefficientRowCompletionOfKrullDimLE_apply_zero
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {d : ℕ} [Ring.KrullDimLE d R] (n : ℕ) (a : Fin (n + 1) → R)
    (ha : Bass.IsRightUnimodular a) (hdn : d + 1 ≤ n)
    (x : Fin (n + 1) → R) :
    coefficientRowCompletionOfKrullDimLE R n a ha hdn x 0 = a ⬝ᵥ x :=
  coefficientRowCompletionOfStableRangeCondition_apply_zero R n a ha
    (Bass.stableRangeCondition_succ_of_krullDimLE (R := R) (d := d)) hdn x

end LinearEquiv

namespace Matrix

universe u

/-- The matrix of the first-coordinate completion of a unimodular row, in
the matrix-completion formulation of Weibel, *The K-book*, I.1.3. -/
noncomputable def coefficientRowCompletionOfStableRangeCondition
    (R : Type u) [CommRing R] (n : ℕ) (a : Fin (n + 1) → R)
    (ha : Bass.IsRightUnimodular a) {s : ℕ}
    (hs : Bass.StableRangeCondition R s) (hsn : s ≤ n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  LinearMap.toMatrix'
    (LinearEquiv.coefficientRowCompletionOfStableRangeCondition R n a ha hs hsn).toLinearMap

/-- The matrix of the inverse of the first-coordinate completion. -/
noncomputable def coefficientRowCompletionInverseOfStableRangeCondition
    (R : Type u) [CommRing R] (n : ℕ) (a : Fin (n + 1) → R)
    (ha : Bass.IsRightUnimodular a) {s : ℕ}
    (hs : Bass.StableRangeCondition R s) (hsn : s ≤ n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  LinearMap.toMatrix'
    (LinearEquiv.coefficientRowCompletionOfStableRangeCondition R n a ha hs hsn).symm.toLinearMap

/-- The completed matrix has first row equal to `a`. -/
@[simp]
theorem coefficientRowCompletionOfStableRangeCondition_row_zero
    (R : Type u) [CommRing R] (n : ℕ) (a : Fin (n + 1) → R)
    (ha : Bass.IsRightUnimodular a) {s : ℕ}
    (hs : Bass.StableRangeCondition R s) (hsn : s ≤ n) :
    coefficientRowCompletionOfStableRangeCondition R n a ha hs hsn 0 = a := by
  funext j
  simp only [coefficientRowCompletionOfStableRangeCondition,
    LinearMap.toMatrix'_apply]
  change (LinearEquiv.coefficientRowCompletionOfStableRangeCondition R n a ha hs hsn
    (Pi.single j 1)) 0 = a j
  simpa only [dotProduct_single_one] using
    (LinearEquiv.coefficientRowCompletionOfStableRangeCondition_apply_zero
      R n a ha hs hsn (Pi.single j 1))

/-- The completed matrix has the displayed matrix as a right inverse. -/
@[simp]
theorem coefficientRowCompletion_mul_inverse
    (R : Type u) [CommRing R] (n : ℕ) (a : Fin (n + 1) → R)
    (ha : Bass.IsRightUnimodular a) {s : ℕ}
    (hs : Bass.StableRangeCondition R s) (hsn : s ≤ n) :
    coefficientRowCompletionOfStableRangeCondition R n a ha hs hsn *
      coefficientRowCompletionInverseOfStableRangeCondition R n a ha hs hsn = 1 := by
  let equiv := LinearEquiv.coefficientRowCompletionOfStableRangeCondition R n a ha hs hsn
  change LinearMap.toMatrix' equiv.toLinearMap *
    LinearMap.toMatrix' equiv.symm.toLinearMap = 1
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
  congr 1
  ext x
  simp

/-- The displayed inverse is also a left inverse of the completed matrix. -/
@[simp]
theorem coefficientRowCompletion_inverse_mul
    (R : Type u) [CommRing R] (n : ℕ) (a : Fin (n + 1) → R)
    (ha : Bass.IsRightUnimodular a) {s : ℕ}
    (hs : Bass.StableRangeCondition R s) (hsn : s ≤ n) :
    coefficientRowCompletionInverseOfStableRangeCondition R n a ha hs hsn *
      coefficientRowCompletionOfStableRangeCondition R n a ha hs hsn = 1 := by
  let equiv := LinearEquiv.coefficientRowCompletionOfStableRangeCondition R n a ha hs hsn
  change LinearMap.toMatrix' equiv.symm.toLinearMap *
    LinearMap.toMatrix' equiv.toLinearMap = 1
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
  congr 1
  ext x
  simp

end Matrix
