/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.RingTheory.Idempotents

/-!
# Decomposition by complete orthogonal projections

A finite complete orthogonal family of linear endomorphisms decomposes a module as the product
of their ranges. The construction uses `DirectSum.Decomposition.ofLinearMap`, followed by the
canonical equivalence between a finite direct sum and a product. Its coordinates are the given
projections, and its inverse sums the inclusions of the ranges.
-/

public section

universe u v w

open scoped BigOperators
open DirectSum

namespace CompleteOrthogonalIdempotents

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {I : Type w} [Fintype I] {p : I → Module.End R M}

section

variable [DecidableEq I]

private def decomposeMap (p : I → Module.End R M) :
    M →ₗ[R] ⨁ i, LinearMap.range (p i) :=
  ∑ i, (DirectSum.lof R I (fun j ↦ LinearMap.range (p j)) i).comp (p i).rangeRestrict

private theorem decomposeMap_apply_coe (x : M) (i : I) :
    ((decomposeMap p x i : LinearMap.range (p i)) : M) = p i x := by
  simp only [decomposeMap, LinearMap.sum_apply, LinearMap.comp_apply,
    DirectSum.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp only [DirectSum.lof_eq_of, DirectSum.of_eq_same]
    rfl
  · intro j _ hji
    rw [DirectSum.lof_eq_of,
      DirectSum.of_eq_of_ne (β := fun k ↦ LinearMap.range (p k)) j i _ hji.symm]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private theorem coeLinearMap_comp_decomposeMap (h : CompleteOrthogonalIdempotents p) :
    (DirectSum.coeLinearMap (fun i ↦ LinearMap.range (p i))).comp (decomposeMap p) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.id_apply, decomposeMap,
    LinearMap.sum_apply, map_sum, DirectSum.coeLinearMap_lof]
  change (∑ i, p i x) = x
  simpa only [LinearMap.sum_apply, Module.End.one_apply] using
    DFunLike.congr_fun h.complete x

private theorem decomposeMap_comp_coeLinearMap (h : CompleteOrthogonalIdempotents p) :
    (decomposeMap p).comp (DirectSum.coeLinearMap (fun i ↦ LinearMap.range (p i))) =
      LinearMap.id := by
  apply DirectSum.linearMap_ext R
  intro j
  apply LinearMap.ext
  intro y
  apply DirectSum.ext
  intro i
  apply Subtype.ext
  change ((decomposeMap p
    (DirectSum.coeLinearMap (fun k ↦ LinearMap.range (p k))
      (DirectSum.lof R I (fun k ↦ LinearMap.range (p k)) j y)) i :
        LinearMap.range (p i)) : M) =
    ((DirectSum.lof R I (fun k ↦ LinearMap.range (p k)) j y i :
        LinearMap.range (p i)) : M)
  rw [DirectSum.coeLinearMap_lof, decomposeMap_apply_coe]
  by_cases hij : i = j
  · subst i
    rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]
    obtain ⟨z, hz⟩ := y.property
    rw [← hz]
    simpa only [Module.End.mul_apply] using
      DFunLike.congr_fun (show p j * p j = p j from h.idem j) z
  · rw [DirectSum.lof_eq_of,
      DirectSum.of_eq_of_ne (β := fun k ↦ LinearMap.range (p k)) j i y hij]
    obtain ⟨z, hz⟩ := y.property
    change p i (y : M) = 0
    rw [← hz]
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using
      DFunLike.congr_fun (h.ortho hij) z

end

/-- A complete orthogonal family of linear projections identifies the module with the product
of their ranges. -/
noncomputable def linearEquivPiRange (h : CompleteOrthogonalIdempotents p) :
    M ≃ₗ[R] ∀ i, LinearMap.range (p i) := by
  classical
  letI : DirectSum.Decomposition (fun i ↦ LinearMap.range (p i)) :=
    DirectSum.Decomposition.ofLinearMap (fun i ↦ LinearMap.range (p i)) (decomposeMap p)
      (coeLinearMap_comp_decomposeMap h) (decomposeMap_comp_coeLinearMap h)
  exact (DirectSum.decomposeLinearEquiv (fun i ↦ LinearMap.range (p i))).trans
    (DirectSum.linearEquivFunOnFintype R I (fun i ↦ LinearMap.range (p i)))

/-- The coordinates of the decomposition are the original projections. -/
@[simp]
theorem linearEquivPiRange_apply_coe (h : CompleteOrthogonalIdempotents p) (x : M) (i : I) :
    (h.linearEquivPiRange x i : M) = p i x := by
  classical
  change (decomposeMap p x i : M) = p i x
  exact decomposeMap_apply_coe x i

/-- Recomposition is the sum of the inclusions of the ranges. -/
@[simp]
theorem linearEquivPiRange_symm_apply (h : CompleteOrthogonalIdempotents p)
    (y : ∀ i, LinearMap.range (p i)) :
    h.linearEquivPiRange.symm y = ∑ i, (y i : M) := by
  calc
    h.linearEquivPiRange.symm y = ∑ i, p i (h.linearEquivPiRange.symm y) := by
      symm
      simpa only [LinearMap.sum_apply, Module.End.one_apply] using
        DFunLike.congr_fun h.complete (h.linearEquivPiRange.symm y)
    _ = ∑ i, (y i : M) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← linearEquivPiRange_apply_coe h (h.linearEquivPiRange.symm y) i,
        LinearEquiv.apply_symm_apply]

end CompleteOrthogonalIdempotents
