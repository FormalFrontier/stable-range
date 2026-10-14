/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.Prod

/-!
# Kernel-product decompositions for split surjective linear maps

A linear map `f : A →ₗ[R] B` with a specified linear right inverse `g` identifies
`ker f × B` with `A`. The forward map sends `(k, b)` to `k + g b`; its inverse
sends `a` to the kernel element `a - g (f a)` together with `f a`. Thus the
original map is retained as the second inverse coordinate, and the first
coordinate depends on the specified section.

The scalar ring need only be a semiring. The source is an additive commutative
group, while the target is only required to be an additive commutative monoid.
The symmetric equivalence gives the decomposition `A ≃ₗ[R] ker f × B`.
For modules over a ring, the construction agrees with Mathlib's equivalence
for a right split exact sequence, after identifying its injective first map
with the kernel.

## Main declarations

* `LinearMap.kerProdEquivOfRightInverse`: the kernel-product equivalence.
* `LinearMap.kerProdEquivOfRightInverse_apply`: its forward formula.
* `LinearMap.kerProdEquivOfRightInverse_symm_fst` and
  `LinearMap.kerProdEquivOfRightInverse_symm_snd`: its inverse coordinates.
* `LinearMap.kerProdEquivOfRightInverse_ofInjective`: comparison with a right
  split exact sequence having an arbitrary injective first map.

## References

* Mathlib, `LinearAlgebra.Prod` and `Algebra.Module.Submodule.Equiv`
  (products, kernels and equivalences with the range of an injective map).
* Mathlib, `Algebra.Category.ModuleCat.Biproducts`,
  `lequivProdOfRightSplitExact` (right split exact sequences of modules).
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter I, §1.2.1 and Theorem I.1.3, for the use of split kernels in
  unimodular rows and high-rank freeness.
* The earlier split-kernel formalization in `StableRange.RowKernel`, by
  Formal Frontier Agents, including Prism.
-/

@[expose] public section

/-- The equivalence of a right split exact sequence sends `(x, b)` to
`j x + g b`, using its specified section `g`. This characterizes the forward
map of Mathlib's `lequivProdOfRightSplitExact`. -/
@[simp]
theorem lequivProdOfRightSplitExact_apply
    {R X A B : Type*} [Ring R]
    [AddCommGroup X] [AddCommGroup B] [AddCommGroup A]
    [Module R X] [Module R B] [Module R A]
    {j : X →ₗ[R] A} {f : A →ₗ[R] B} {g : B →ₗ[R] A}
    (hj : Function.Injective j) (hexac : LinearMap.range j = LinearMap.ker f)
    (hfg : f.comp g = LinearMap.id) (x : X) (b : B) :
    _root_.lequivProdOfRightSplitExact (j := j) (g := f) (f := g) hj hexac hfg
      (x, b) = j x + g b := by
  -- The universe lifts preserve the given section, and the inverse of the
  -- splitting isomorphism is the biproduct descendent of `j` and `g`.
  change
    ((CategoryTheory.CategoryStruct.comp (ModuleCat.biprodIsoProd _ _).inv
      (CategoryTheory.Limits.biprod.desc
        (ModuleCat.ofHom
          (ULift.moduleEquiv.symm.toLinearMap ∘ₗ j ∘ₗ ULift.moduleEquiv.toLinearMap))
        (ModuleCat.ofHom
          (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ ULift.moduleEquiv.toLinearMap)))).hom
      (ULift.up x, ULift.up b)).down = j x + g b
  rw [CategoryTheory.Limits.biprod.desc_eq, CategoryTheory.Preadditive.comp_add]
  simp only [← CategoryTheory.Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst,
    ModuleCat.biprodIsoProd_inv_comp_snd, ModuleCat.hom_add, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearEquiv.coe_toLinearMap,
    ULift.moduleEquiv_apply, ULift.moduleEquiv_symm_apply]
  rfl

namespace LinearMap

/-- The kernel-product equivalence of a linear map with a specified right
inverse. It sends `(k, b)` to `k + g b`, and its inverse has coordinates
`a - g (f a)` and `f a`. The splitting formula used for row kernels in
Weibel's *The K-book*, Chapter I, §1.2.1 and Theorem I.1.3, only requires a
semiring of scalars, an additive group source and an additive monoid target. -/
noncomputable def kerProdEquivOfRightInverse
    {R A B : Type*} [Semiring R]
    [AddCommGroup A] [Module R A] [AddCommMonoid B] [Module R B]
    (f : A →ₗ[R] B) (g : B →ₗ[R] A)
    (hfg : f.comp g = LinearMap.id) :
    (f.ker × B) ≃ₗ[R] A := by
  let φ : (f.ker × B) →ₗ[R] A := f.ker.subtype.coprod g
  have hfg' (b : B) : f (g b) = b := by
    simpa using LinearMap.congr_fun hfg b
  have hg : Function.Injective g := g.injective_of_comp_eq_id f hfg
  let kproj : A →ₗ[R] f.ker :=
    LinearMap.codRestrict f.ker (LinearMap.id - g.comp f) fun a ↦ by
      rw [mem_ker]
      apply hg
      change (g.comp f) (a - g (f a)) = g 0
      rw [map_sub]
      simp only [comp_apply, hfg', map_zero, sub_self]
  let ψ : A →ₗ[R] (f.ker × B) := kproj.prod f
  exact LinearEquiv.ofLinearMap φ ψ
    (by
      apply LinearMap.ext
      intro a
      change (a - g (f a)) + g (f a) = a
      exact sub_add_cancel a (g (f a)))
    (by
      apply LinearMap.ext
      intro p
      apply Prod.ext
      · apply Subtype.ext
        change (p.1.val + g p.2) - g (f (p.1.val + g p.2)) = p.1.val
        rw [map_add, mem_ker.mp p.1.2, zero_add, hfg']
        exact add_sub_cancel_right _ _
      · change f (p.1.val + g p.2) = p.2
        rw [map_add, mem_ker.mp p.1.2, zero_add, hfg'])

/-- The kernel-product equivalence adds the kernel element to the image of
the specified section. -/
@[simp]
theorem kerProdEquivOfRightInverse_apply
    {R A B : Type*} [Semiring R]
    [AddCommGroup A] [Module R A] [AddCommMonoid B] [Module R B]
    (f : A →ₗ[R] B) (g : B →ₗ[R] A)
    (hfg : f.comp g = LinearMap.id) (p : f.ker × B) :
    kerProdEquivOfRightInverse f g hfg p = p.1.1 + g p.2 := by
  rfl

/-- The first inverse coordinate is the section-dependent kernel element,
whose underlying value is `a - g (f a)`. -/
@[simp]
theorem kerProdEquivOfRightInverse_symm_fst
    {R A B : Type*} [Semiring R]
    [AddCommGroup A] [Module R A] [AddCommMonoid B] [Module R B]
    (f : A →ₗ[R] B) (g : B →ₗ[R] A)
    (hfg : f.comp g = LinearMap.id) (a : A) :
    ((kerProdEquivOfRightInverse f g hfg).symm a).1.val = a - g (f a) := by
  rfl

/-- The second inverse coordinate is the original linear map. -/
@[simp]
theorem kerProdEquivOfRightInverse_symm_snd
    {R A B : Type*} [Semiring R]
    [AddCommGroup A] [Module R A] [AddCommMonoid B] [Module R B]
    (f : A →ₗ[R] B) (g : B →ₗ[R] A)
    (hfg : f.comp g = LinearMap.id) (a : A) :
    ((kerProdEquivOfRightInverse f g hfg).symm a).2 = f a := by
  rfl

/-- Identifying an injective first map with the kernel transports the
kernel-product equivalence to Mathlib's `lequivProdOfRightSplitExact`.
Both equivalences use the same specified section `g` of `f`. -/
theorem kerProdEquivOfRightInverse_ofInjective
    {R X A B : Type*} [Ring R]
    [AddCommGroup X] [AddCommGroup B] [AddCommGroup A]
    [Module R X] [Module R B] [Module R A]
    {j : X →ₗ[R] A} {f : A →ₗ[R] B} {g : B →ₗ[R] A}
    (hj : Function.Injective j) (hexac : LinearMap.range j = f.ker)
    (hfg : f.comp g = LinearMap.id) :
    (((LinearEquiv.ofInjective j hj).trans
      (LinearEquiv.ofEq j.range f.ker hexac)).prodCongr
        (LinearEquiv.refl R B)).trans (kerProdEquivOfRightInverse f g hfg) =
      _root_.lequivProdOfRightSplitExact (j := j) (g := f) (f := g) hj hexac hfg := by
  apply LinearEquiv.ext
  rintro ⟨x, b⟩
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, kerProdEquivOfRightInverse_apply,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply,
    _root_.lequivProdOfRightSplitExact_apply]

end LinearMap
