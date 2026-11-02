/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Module.SplitSurjective
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Ranks of complementary ranges for specified splittings

For linear maps `f : A →ₗ[K] E` and `g : E →ₗ[K] A` with `f.comp g = id`,
the complementary endomorphism `id - g.comp f` has range of dimension
`finrank K A - finrank K E`. Only the ambient module `A` is assumed
finite-dimensional; finite-dimensionality of `E` follows from the split
surjection. The rank formula follows from the specified-section
kernel-product equivalence and product finrank.

For a family of targets `E b` with given equivalences `E b ≃ₗ[K] F`, the
same formula holds at every `b`, with `finrank K F` subtracted. The base can
be empty and no finite-dimensionality assumption on `F` is needed.

## References

* `StableRange.Module.SplitSurjective`, for the kernel-product equivalence
  and its complementary-range characterization.
* Mathlib, `Algebra.Module.NatInt`, for the additive group structure induced
  by a ring action.
* Mathlib, `LinearAlgebra.Dimension.Constructions` and
  `LinearAlgebra.FiniteDimensional.Defs`, for product finrank, invariance
  under linear equivalence and finite-dimensionality of a surjective image.
-/

@[expose] public section

namespace LinearMap

universe uK uA uE uB uF

/-- The complementary range of a specified split surjection has dimension
`finrank K A - finrank K E`. Finite-dimensionality of the target follows
from the given section. The target needs only its given additive monoid
and module structures. -/
theorem finrank_range_id_sub_comp_of_rightInverse
    {K : Type uK} [DivisionRing K]
    {A : Type uA} [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    {E : Type uE} [AddCommMonoid E] [Module K E]
    (f : A →ₗ[K] E) (g : E →ₗ[K] A)
    (hfg : f.comp g = LinearMap.id) :
    Module.finrank K (LinearMap.range (LinearMap.id - g.comp f)) =
      Module.finrank K A - Module.finrank K E := by
  let : AddCommGroup E := Module.addCommMonoidToAddCommGroup K (M := E)
  let : FiniteDimensional K E := FiniteDimensional.of_surjective f
    (fun e ↦ ⟨g e, LinearMap.congr_fun hfg e⟩)
  rw [range_id_sub_comp_eq_ker_of_rightInverse f g hfg]
  apply eq_tsub_of_add_eq
  rw [← Module.finrank_prod]
  exact (kerProdEquivOfRightInverse f g hfg).finrank_eq

/-- Complementary ranges in a family of specified splittings have the
ambient dimension minus the dimension of a given common model. The base
is arbitrary, and the model need not be assumed finite-dimensional. -/
theorem finrank_range_id_sub_comp_of_rightInverse_family
    {K : Type uK} [DivisionRing K]
    {A : Type uA} [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    {B : Type uB} {E : B → Type uE}
    [∀ b, AddCommMonoid (E b)] [∀ b, Module K (E b)]
    {F : Type uF} [AddCommMonoid F] [Module K F]
    (f : ∀ b, A →ₗ[K] E b) (g : ∀ b, E b →ₗ[K] A)
    (hfg : ∀ b, (f b).comp (g b) = LinearMap.id)
    (e : ∀ b, E b ≃ₗ[K] F) :
    ∀ b, Module.finrank K (LinearMap.range (LinearMap.id - (g b).comp (f b))) =
      Module.finrank K A - Module.finrank K F := by
  intro b
  rw [finrank_range_id_sub_comp_of_rightInverse (f b) (g b) (hfg b),
    (e b).finrank_eq]

end LinearMap
