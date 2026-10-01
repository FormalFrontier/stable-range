/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Regular
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection

/-!
# Regular endomorphism and matrix rings over division rings

This file proves that every endomorphism of an arbitrary vector space over a
division ring has an inner inverse, so its endomorphism ring is von
Neumann-regular. In finite dimension the inner inverse can be chosen to be an
automorphism. Via the right-linear matrix equivalence, it follows that every
finite square matrix ring over a division ring is unit-regular.
-/

set_option warningAsError true

@[expose] public section

open Function

universe u v

namespace LinearMap

variable {K : Type u} [DivisionRing K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- Every endomorphism of a vector space over a division ring has an inner
inverse. No finite-dimensional hypothesis is needed. -/
theorem exists_innerInverse (f : Module.End K V) :
    ∃ g : Module.End K V, f = f * g * f := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (ker f)
  let fC : C →ₗ[K] range f := f.rangeRestrict.domRestrict C
  have hfC_injective : Injective fC := by
    intro x y hxy
    apply (injective_domRestrict_iff.mpr hC.disjoint.symm)
    exact congrArg Subtype.val hxy
  have hrange : range (f.domRestrict C) = range f :=
    (range_domRestrict C f).trans
      (Submodule.map_eq_range_iff.mpr hC.codisjoint.symm)
  have hfC_surjective : Surjective fC := by
    intro y
    have hy : (y : V) ∈ range (f.domRestrict C) := by
      rw [hrange]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  let e : C ≃ₗ[K] range f :=
    LinearEquiv.ofBijective fC ⟨hfC_injective, hfC_surjective⟩
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (range f)
  let g : Module.End K V := C.subtype.comp
    (e.symm.toLinearMap.comp ((range f).projectionOnto D hD))
  refine ⟨g, ?_⟩
  apply ext
  intro x
  change f x = f (g (f x))
  let y : range f := ⟨f x, ⟨x, rfl⟩⟩
  have hproj : (range f).projectionOnto D hD (f x) = y :=
    Submodule.projectionOnto_apply_of_mem_left hD y.property
  have hg : g (f x) = (e.symm y : V) := by
    change (C.subtype (e.symm ((range f).projectionOnto D hD (f x))) : V) = _
    rw [hproj]
    rfl
  rw [hg]
  change f x = f (e.symm y)
  exact congrArg Subtype.val (e.apply_symm_apply y).symm

variable [FiniteDimensional K V]

/-- Every endomorphism of a finite-dimensional vector space over a division
ring has an automorphic inner inverse. -/
theorem exists_linearEquiv_innerInverse (f : Module.End K V) :
    ∃ g : V ≃ₗ[K] V, ∀ x, f (g (f x)) = f x := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (ker f)
  let fC : C →ₗ[K] range f := f.rangeRestrict.domRestrict C
  have hfC_injective : Injective fC := by
    intro x y hxy
    apply (injective_domRestrict_iff.mpr hC.disjoint.symm)
    exact congrArg Subtype.val hxy
  have hrange : range (f.domRestrict C) = range f :=
    (range_domRestrict C f).trans
      (Submodule.map_eq_range_iff.mpr hC.codisjoint.symm)
  have hfC_surjective : Surjective fC := by
    intro y
    have hy : (y : V) ∈ range (f.domRestrict C) := by
      rw [hrange]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  let e : C ≃ₗ[K] range f :=
    LinearEquiv.ofBijective fC ⟨hfC_injective, hfC_surjective⟩
  obtain ⟨g, hg⟩ :=
    Submodule.exists_linearEquiv_restrict_eq e.symm
  refine ⟨g, fun x ↦ ?_⟩
  let y : range f := ⟨f x, ⟨x, rfl⟩⟩
  have hgy : g (y : V) = (e.symm y : C) := (hg y).symm
  rw [show f x = (y : V) by rfl, hgy]
  change f (e.symm y) = (y : V)
  exact congrArg Subtype.val (e.apply_symm_apply y)

end LinearMap

namespace Bass

variable {K : Type u} [DivisionRing K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The endomorphism ring of every vector space over a division ring is von
Neumann-regular. No finite-dimensional hypothesis is needed. -/
theorem isVonNeumannRegular_moduleEnd :
    IsVonNeumannRegular (Module.End K V) :=
  LinearMap.exists_innerInverse

variable {n : Type v} [Fintype n] [DecidableEq n]

/-- Every finite square matrix ring over a division ring is unit-regular. -/
theorem isUnitRegular_matrix : IsUnitRegular (Matrix n n K) := by
  intro A
  let f : Module.End K (n → K) := A.toLinearMapRight'
  obtain ⟨g, hg⟩ := f.exists_linearEquiv_innerInverse
  let U : Matrix n n K := LinearMap.toMatrixRight' g.toLinearMap
  let Uinv : Matrix n n K := LinearMap.toMatrixRight' g.symm.toLinearMap
  have hU_Uinv : U * Uinv = 1 := by
    change LinearMap.toMatrixRight' g.toLinearMap *
      LinearMap.toMatrixRight' g.symm.toLinearMap = 1
    rw [← LinearMap.toMatrixRight'_comp]
    simp
  have hUinv_U : Uinv * U = 1 := by
    change LinearMap.toMatrixRight' g.symm.toLinearMap *
      LinearMap.toMatrixRight' g.toLinearMap = 1
    rw [← LinearMap.toMatrixRight'_comp]
    simp
  have hU : Matrix.toLinearMapRight' U = g.toLinearMap := by
    change Matrix.toLinearMapRight' (LinearMap.toMatrixRight' g.toLinearMap) =
      g.toLinearMap
    exact (Matrix.toLinearMapRight' (R := K)).apply_symm_apply g.toLinearMap
  let unit : (Matrix n n K)ˣ := ⟨U, Uinv, hU_Uinv, hUinv_U⟩
  refine ⟨unit, ?_⟩
  change A = A * U * A
  apply (Matrix.toLinearMapRight' (R := K)).injective
  apply LinearMap.ext
  intro x
  simpa only [f, Matrix.toLinearMapRight'_mul_apply, hU,
    LinearEquiv.coe_toLinearMap] using (hg x).symm

end Bass
