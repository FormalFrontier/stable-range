/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.RowKernel
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Algebra.Module.Equiv.Opposite

/-!
# Rectangular completion of right-coefficient rows

A specified right-inverse column and coordinates on the right-linear kernel give
coordinate-preserving rectangular inverse matrices. Conversely, such matrices
give coordinates on the kernel. The rank of the kernel is not assumed to be
one less than the length of the row: that conclusion would require invariant
basis number. The commutative square-matrix result in `StableRange.RowKernel`
has a comparison with this construction.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  August 29, 2013 complete-book build, I.1.2.1 (free-kernel/basis-extension
  proof idea for unimodular row completion).
* Mathlib, `LinearAlgebra.Matrix.ToLin`, `LinearAlgebra.Pi` and
  `LinearAlgebra.FreeModule.Finite.Basic` (right-linear matrix actions, finite
  coordinates and free bases).
-/

set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace LinearEquiv

universe u

/-- The original coefficient row, its specified section and the selected kernel
coordinates, assembled into a right-linear coordinate equivalence. The head
coordinate is the coefficient functional. -/
noncomputable def rightCoefficientRowCoordinates (R : Type u) [Ring R]
    {n m : ℕ} (a b : Fin n → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R)) :
    (Fin n → R) ≃ₗ[Rᵐᵒᵖ] (Fin (m + 1) → R) :=
  ((rightCoefficientKernelProd R a b hb).symm).trans
    ((e.prodCongr (LinearEquiv.refl Rᵐᵒᵖ R)).trans
      ((LinearEquiv.prodComm Rᵐᵒᵖ (Fin m → R) R).trans
        (Fin.consLinearEquiv Rᵐᵒᵖ (fun _ : Fin (m + 1) ↦ R))))

/-- The first chosen coordinate is precisely the original coefficient row. -/
@[simp]
theorem rightCoefficientRowCoordinates_zero (R : Type u) [Ring R]
    {n m : ℕ} (a b : Fin n → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R))
    (x : Fin n → R) :
    rightCoefficientRowCoordinates R a b hb e x 0 =
      dotProductBilin R Rᵐᵒᵖ a x := by
  simp [rightCoefficientRowCoordinates,
    rightCoefficientKernelProd_symm_snd]

/-- The remaining chosen coordinates are the coordinates of the original
section-dependent kernel projection. -/
@[simp]
theorem rightCoefficientRowCoordinates_succ (R : Type u) [Ring R]
    {n m : ℕ} (a b : Fin n → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R))
    (x : Fin n → R) (j : Fin m) :
    rightCoefficientRowCoordinates R a b hb e x (Fin.succ j) =
      e ((rightCoefficientKernelProd R a b hb).symm x).1 j := by
  simp [rightCoefficientRowCoordinates]

/-- The tail coordinates use the specified witness, with multiplication on the
left of the original row value, before applying the supplied kernel coordinates. -/
theorem rightCoefficientRowCoordinates_succ_projection (R : Type u) [Ring R]
    {n m : ℕ} (a b : Fin n → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R))
    (x : Fin n → R) (j : Fin m) :
    rightCoefficientRowCoordinates R a b hb e x (Fin.succ j) =
      e ⟨x - (fun i ↦ b i * dotProductBilin R Rᵐᵒᵖ a x),
        rightCoefficientKernelProd_symm_fst_mem R a b hb x⟩ j := by
  rw [rightCoefficientRowCoordinates_succ,
    rightCoefficientKernelProd_symm_fst_subtype]

/-- Rebuilding a column from its original scalar and chosen kernel
coordinates uses the supplied witness, on the left of that scalar. -/
@[simp]
theorem rightCoefficientRowCoordinates_symm_apply (R : Type u) [Ring R]
    {n m : ℕ} (a b : Fin n → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R))
    (y : Fin (m + 1) → R) (i : Fin n) :
    (rightCoefficientRowCoordinates R a b hb e).symm y i =
      b i * y 0 + (e.symm (Fin.tail y)).1 i := by
  simp [rightCoefficientRowCoordinates, rightCoefficientKernelProd_apply,
    add_comm]

end LinearEquiv

namespace Matrix

universe u

private theorem mulVec_of_rightLinearMap (R : Type u) [Ring R]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → R) →ₗ[Rᵐᵒᵖ] (κ → R)) (x : ι → R) :
    (fun i j ↦ f (Pi.single j (1 : R)) i) *ᵥ x = f x := by
  ext i
  calc
    ((fun i j ↦ f (Pi.single j (1 : R)) i) *ᵥ x) i =
        ∑ j, f (Pi.single j (1 : R)) i * x j := rfl
    _ = ∑ j, f (Pi.single j (x j)) i := by
      apply Finset.sum_congr rfl
      intro j _
      have h : (Pi.single j (x j) : ι → R) =
          MulOpposite.op (x j) • (Pi.single j (1 : R) : ι → R) := by
        ext k
        simp [Pi.single_apply]
      rw [h, map_smul, Pi.smul_apply, op_smul_eq_mul]
    _ = f (∑ j, Pi.single j (x j)) i := by rw [map_sum, Finset.sum_apply]
    _ = f x i := by rw [LinearMap.sum_single_apply]

/-- The matrix of the specified right-linear row coordinates. Each column is
the image of a standard coordinate column. -/
noncomputable def rightRowCompletion (R : Type u) [Ring R]
    {n m : ℕ} (a b : Fin n → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R)) :
    Matrix (Fin (m + 1)) (Fin n) R :=
  fun i j ↦ LinearEquiv.rightCoefficientRowCoordinates R a b hb e (Pi.single j 1) i

/-- The matrix reconstructing the original column from scalar and selected
kernel coordinates. -/
noncomputable def rightRowCompletionInv (R : Type u) [Ring R]
    {n m : ℕ} (a b : Fin n → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R)) :
    Matrix (Fin n) (Fin (m + 1)) R :=
  fun i j ↦ (LinearEquiv.rightCoefficientRowCoordinates R a b hb e).symm
    (Pi.single j 1) i

@[simp]
theorem rightRowCompletion_apply (R : Type u) [Ring R]
    {n m : ℕ} (a b : Fin n → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R))
    (i : Fin (m + 1)) (j : Fin n) :
    rightRowCompletion R a b hb e i j =
      LinearEquiv.rightCoefficientRowCoordinates R a b hb e (Pi.single j 1) i := rfl

@[simp]
theorem rightRowCompletionInv_apply (R : Type u) [Ring R]
    {n m : ℕ} (a b : Fin n → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R))
    (i : Fin n) (j : Fin (m + 1)) :
    rightRowCompletionInv R a b hb e i j =
      (LinearEquiv.rightCoefficientRowCoordinates R a b hb e).symm (Pi.single j 1) i := rfl

/-- The completion acts by the supplied coordinate equivalence, on right
coefficient columns. -/
theorem rightRowCompletion_mulVec (R : Type u) [Ring R]
    {n m : ℕ} (a b : Fin n → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R))
    (x : Fin n → R) :
    rightRowCompletion R a b hb e *ᵥ x =
      LinearEquiv.rightCoefficientRowCoordinates R a b hb e x := by
  exact mulVec_of_rightLinearMap R
    (LinearEquiv.rightCoefficientRowCoordinates R a b hb e).toLinearMap x

/-- The inverse completion reconstructs the column using the chosen
coordinates. -/
theorem rightRowCompletionInv_mulVec (R : Type u) [Ring R]
    {n m : ℕ} (a b : Fin n → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R))
    (y : Fin (m + 1) → R) :
    rightRowCompletionInv R a b hb e *ᵥ y =
      (LinearEquiv.rightCoefficientRowCoordinates R a b hb e).symm y := by
  exact mulVec_of_rightLinearMap R
    (LinearEquiv.rightCoefficientRowCoordinates R a b hb e).symm.toLinearMap y

/-- The specified row remains the first row of the completion. -/
theorem rightRowCompletion_zero (R : Type u) [Ring R]
    {n m : ℕ} (a b : Fin n → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R)) :
    rightRowCompletion R a b hb e 0 = a := by
  funext j
  rw [rightRowCompletion_apply, LinearEquiv.rightCoefficientRowCoordinates_zero]
  simp [dotProductBilin]

/-- The specified witness remains the first column of the inverse. -/
theorem rightRowCompletionInv_zero (R : Type u) [Ring R]
    {n m : ℕ} (a b : Fin n → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R)) :
    (fun i ↦ rightRowCompletionInv R a b hb e i 0) = b := by
  funext i
  rw [rightRowCompletionInv_apply, LinearEquiv.rightCoefficientRowCoordinates_symm_apply]
  have ht : Fin.tail (Pi.single 0 (1 : R) : Fin (m + 1) → R) = 0 := by
    funext j
    simp [Fin.tail]
  rw [ht]
  simp

/-- The completion and its inverse multiply to the identity on the selected
coordinates. -/
theorem rightRowCompletion_mul_inv (R : Type u) [Ring R]
    {n m : ℕ} (a b : Fin n → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R)) :
    rightRowCompletion R a b hb e * rightRowCompletionInv R a b hb e = 1 := by
  apply Matrix.ext
  intro i j
  have h' : (rightRowCompletion R a b hb e * rightRowCompletionInv R a b hb e) *ᵥ
      Pi.single j 1 = Pi.single j 1 := by
    rw [← Matrix.mulVec_mulVec, rightRowCompletionInv_mulVec,
      rightRowCompletion_mulVec, LinearEquiv.apply_symm_apply]
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply,
    eq_comm] using congrFun h' i

/-- The inverse and completion multiply to the identity on the original
coordinates. -/
theorem rightRowCompletion_inv_mul (R : Type u) [Ring R]
    {n m : ℕ} (a b : Fin n → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R)) :
    rightRowCompletionInv R a b hb e * rightRowCompletion R a b hb e = 1 := by
  apply Matrix.ext
  intro i j
  have h' : (rightRowCompletionInv R a b hb e * rightRowCompletion R a b hb e) *ᵥ
      Pi.single j 1 = Pi.single j 1 := by
    rw [← Matrix.mulVec_mulVec, rightRowCompletion_mulVec,
      rightRowCompletionInv_mulVec, LinearEquiv.symm_apply_apply]
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply,
    eq_comm] using congrFun h' i

end Matrix

namespace LinearEquiv

universe u

/-- A rectangular two-sided inverse with a specified first row identifies
the kernel of its right coefficient functional with the remaining coordinates. -/
noncomputable def rightCoefficientKernelEquivOfMatrixInverse (R : Type u) [Ring R]
    {n m : ℕ} (a : Fin n → R)
    (A : Matrix (Fin (m + 1)) (Fin n) R)
    (B : Matrix (Fin n) (Fin (m + 1)) R)
    (hrow : A 0 = a) (hAB : A * B = 1) (hBA : B * A = 1) :
    LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R) := by
  let inverse (y : Fin m → R) :
      LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) :=
    ⟨B *ᵥ Fin.cons 0 y, by
      rw [LinearMap.mem_ker]
      change a ⬝ᵥ (B *ᵥ Fin.cons 0 y) = 0
      rw [← hrow]
      change (A *ᵥ (B *ᵥ Fin.cons 0 y)) 0 = 0
      rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
      rfl⟩
  refine {
    toFun := fun x ↦ Fin.tail (A *ᵥ x.1)
    invFun := inverse
    map_add' := ?_
    map_smul' := ?_
    left_inv := ?_
    right_inv := ?_ }
  · intro x y
    ext j
    simp only [Submodule.coe_add, Matrix.mulVec_add]
    change (A *ᵥ x.1 + A *ᵥ y.1) (Fin.succ j) =
      (A *ᵥ x.1) (Fin.succ j) + (A *ᵥ y.1) (Fin.succ j)
    rfl
  · intro c x
    ext j
    simp only [Submodule.coe_smul, Matrix.mulVec_smul]
    change (c • (A *ᵥ x.1)) (Fin.succ j) =
      (A *ᵥ x.1) (Fin.succ j) * c.unop
    rfl
  · intro x
    apply Subtype.ext
    change B *ᵥ Fin.cons 0 (Fin.tail (A *ᵥ x.1)) = x.1
    have head : (A *ᵥ x.1) 0 = 0 := by
      change A 0 ⬝ᵥ x.1 = 0
      rw [hrow]
      exact LinearMap.mem_ker.mp x.2
    rw [← head, Fin.cons_self_tail, Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  · intro y
    change Fin.tail (A *ᵥ (B *ᵥ Fin.cons 0 y)) = y
    rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec, Fin.tail_cons]

/-- The forward kernel coordinate is the tail of the original matrix
action. -/
@[simp]
theorem rightCoefficientKernelEquivOfMatrixInverse_apply (R : Type u) [Ring R]
    {n m : ℕ} (a : Fin n → R)
    (A : Matrix (Fin (m + 1)) (Fin n) R)
    (B : Matrix (Fin n) (Fin (m + 1)) R)
    (hrow : A 0 = a) (hAB : A * B = 1) (hBA : B * A = 1)
    (x : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a)) :
    rightCoefficientKernelEquivOfMatrixInverse R a A B hrow hAB hBA x =
      Fin.tail (A *ᵥ x.1) := by
  rfl

/-- The inverse kernel coordinate applies the original inverse matrix to
the column with zero head. -/
@[simp]
theorem rightCoefficientKernelEquivOfMatrixInverse_symm_apply (R : Type u) [Ring R]
    {n m : ℕ} (a : Fin n → R)
    (A : Matrix (Fin (m + 1)) (Fin n) R)
    (B : Matrix (Fin n) (Fin (m + 1)) R)
    (hrow : A 0 = a) (hAB : A * B = 1) (hBA : B * A = 1)
    (y : Fin m → R) :
    ((rightCoefficientKernelEquivOfMatrixInverse R a A B hrow hAB hBA).symm y).1 =
      B *ᵥ Fin.cons 0 y := by
  rfl

end LinearEquiv

namespace Matrix

universe u

/-- A right inverse matrix supplies a right-unimodularity witness for its
distinguished row. A left inverse is not needed for this direction. -/
theorem isRightUnimodular_of_rectangular_inverse (R : Type u) [Ring R]
    {n m : ℕ} (a : Fin n → R)
    (A : Matrix (Fin (m + 1)) (Fin n) R)
    (B : Matrix (Fin n) (Fin (m + 1)) R)
    (hrow : A 0 = a) (hAB : A * B = 1) :
    Bass.IsRightUnimodular a := by
  refine ⟨fun i ↦ B i 0, ?_⟩
  have h := congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) R ↦ M 0 0) hAB
  change (∑ i, A 0 i * B i 0) = 1 at h
  simpa only [dotProductBilin, dotProduct, hrow] using h

end Matrix

namespace LinearMap

universe u

/-- The split finite free column module makes the kernel of a right-unimodular
row finitely generated. This is a consequence, not a hypothesis of completion. -/
theorem finite_rightCoefficientKernel (R : Type u) [Ring R]
    {n : ℕ} (a : Fin n → R) (ha : Bass.IsRightUnimodular a) :
    Module.Finite Rᵐᵒᵖ (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a)) := by
  classical
  have : Module.Finite Rᵐᵒᵖ R :=
    Module.Finite.of_surjective
      (MulOpposite.opLinearEquiv Rᵐᵒᵖ (M := R)).symm.toLinearMap
      (MulOpposite.opLinearEquiv Rᵐᵒᵖ (M := R)).symm.surjective
  obtain ⟨b, hb⟩ := ha
  apply Module.Finite.of_surjective
    ((LinearMap.fst Rᵐᵒᵖ
      (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a)) R).comp
      (LinearEquiv.rightCoefficientKernelProd R a b hb).symm.toLinearMap)
  intro x
  refine ⟨LinearEquiv.rightCoefficientKernelProd R a b hb (x, 0), ?_⟩
  simp

end LinearMap

namespace Matrix

universe u

/-- Right-unimodularity and freeness of the right coefficient kernel are
equivalent to a two-sided rectangular completion with the original first row.
No equality of the row length and the number of chosen coordinates is assumed.
The free-kernel/basis-extension proof idea follows C. A. Weibel, *The K-book:
An Introduction to Algebraic K-theory* (August 29, 2013 complete-book build),
I.1.2.1. This rectangular result does not settle the book's dimension-unspecified
wording outside invariant-basis-number rings. -/
theorem isRightUnimodular_and_free_kernel_iff_exists_rectangular_inverse
    (R : Type u) [Ring R] {n : ℕ} (a : Fin n → R) :
    (Bass.IsRightUnimodular a ∧
      Module.Free Rᵐᵒᵖ (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a))) ↔
      ∃ (m : ℕ) (A : Matrix (Fin (m + 1)) (Fin n) R)
        (B : Matrix (Fin n) (Fin (m + 1)) R),
        A 0 = a ∧ A * B = 1 ∧ B * A = 1 := by
  constructor
  · rintro ⟨⟨b, hb⟩, hfree⟩
    have : Module.Free Rᵐᵒᵖ
        (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a)) := hfree
    have : Module.Finite Rᵐᵒᵖ
        (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a)) :=
      LinearMap.finite_rightCoefficientKernel R a ⟨b, hb⟩
    have : Module.Free Rᵐᵒᵖ R :=
      Module.Free.of_equiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ (M := R)).symm
    let ι := Module.Free.ChooseBasisIndex Rᵐᵒᵖ
      (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a))
    have : Fintype ι := Module.Free.ChooseBasisIndex.fintype Rᵐᵒᵖ
      (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a))
    let m := Fintype.card ι
    let e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ]
        (Fin m → R) :=
      ((Module.Free.chooseBasis Rᵐᵒᵖ _).repr).trans
        ((Finsupp.linearEquivFunOnFinite Rᵐᵒᵖ Rᵐᵒᵖ ι).trans
          ((LinearEquiv.piCongrRight
            (fun _ : ι ↦ (MulOpposite.opLinearEquiv Rᵐᵒᵖ (M := R)).symm)).trans
            (LinearEquiv.piCongrLeft Rᵐᵒᵖ (fun _ : Fin m ↦ R)
              (Fintype.equivFin ι))))
    refine ⟨m, rightRowCompletion R a b hb e, rightRowCompletionInv R a b hb e,
      rightRowCompletion_zero R a b hb e, ?_, ?_⟩
    · exact rightRowCompletion_mul_inv R a b hb e
    · exact rightRowCompletion_inv_mul R a b hb e
  · rintro ⟨m, A, B, hrow, hAB, hBA⟩
    have : Module.Free Rᵐᵒᵖ R :=
      Module.Free.of_equiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ (M := R)).symm
    exact ⟨isRightUnimodular_of_rectangular_inverse R a A B hrow hAB,
      Module.Free.of_equiv
        (LinearEquiv.rightCoefficientKernelEquivOfMatrixInverse R a A B hrow hAB hBA).symm⟩

end Matrix

namespace LinearEquiv

universe u

/-- In the commutative square case, the rectangular kernel coordinates are
the first-row coordinates of `Bass.coefficientRowKernelEquivOfMatrixInverse`
after applying the existing `LinearMap.coefficientRowKernelAddEquiv`. -/
theorem rightCoefficientKernelEquivOfMatrixInverse_comm (R : Type u) [CommRing R]
    {m : ℕ} (a : Fin (m + 1) → R)
    (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (hrow : A 0 = a) (hAB : A * B = 1) (hBA : B * A = 1)
    (x : LinearMap.ker (Bass.coefficientRowScalarMap R (m + 1) a))
    (j : Fin m) :
    rightCoefficientKernelEquivOfMatrixInverse R a A B hrow hAB hBA
        (LinearMap.coefficientRowKernelAddEquiv R a x) j =
      Bass.coefficientRowKernelEquivOfMatrixInverse R (m + 1) 0 a A B
        hrow hAB hBA
        ⟨x.1, by rw [← Bass.ker_coefficientRowScalarMap_eq]; exact x.2⟩
        ⟨Fin.succ j, by simp⟩ := by
  rw [rightCoefficientKernelEquivOfMatrixInverse_apply]
  simp [Bass.coefficientRowKernelEquivOfMatrixInverse,
    Bass.coordinateHyperplaneEquiv, Bass.kernelEquivOfLinearEquiv,
    LinearMap.iInfKerProjEquiv, Fin.tail]

end LinearEquiv
