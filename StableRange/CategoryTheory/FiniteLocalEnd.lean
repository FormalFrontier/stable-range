/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Basic
import StableRange.Semisimple
public import StableRange.Module.LocalEnd
public import StableRange.Module.Corner
public import StableRange.Module.Decomposition
public import StableRange.Module.SemisimpleQuotient
public import StableRange.CategoryTheory.EndCorner
public import StableRange.CategoryTheory.EndRetract
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.LocalRing.Defs

/-!
# Stable range of finite biproduct endomorphism rings

The endomorphism ring of a finite biproduct of objects with local endomorphism rings
satisfies Bass's stable range condition in degree one. The same conclusion holds
for every displayed retract of that biproduct.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open Limits

/-- A finite biproduct of objects with local endomorphism rings has an endomorphism ring
satisfying Bass's stable range condition in degree one. -/
theorem stableRangeCondition_one_end_biproduct
    {C : Type u} [Category.{v} C] [Preadditive C]
    {ι : Type w} [Finite ι] (F : ι → C) [HasBiproduct F]
    (h : ∀ i, IsLocalRing (End (F i))) :
    Bass.StableRangeCondition (End (biproduct F)) 1 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let R := End (biproduct F)
  let e : ι → R := fun i => biproduct.π F i ≫ biproduct.ι F i
  have he : CompleteOrthogonalIdempotents e := biproduct.completeOrthogonalIdempotents F
  let p : ι → Module.End R R := fun i =>
    RingEquiv.moduleEndSelf R (MulOpposite.op (e i))
  have hp_apply (i : ι) (x : R) : p i x = x * e i := rfl
  have hp : CompleteOrthogonalIdempotents p := by
    refine {
      idem := fun i => (he.idem i).op.map (RingEquiv.moduleEndSelf R)
      ortho := ?_
      complete := ?_
    }
    · intro i j hij
      apply LinearMap.ext
      intro x
      simp only [Module.End.mul_apply, hp_apply, LinearMap.zero_apply]
      rw [mul_assoc, he.ortho hij.symm, mul_zero]
    · apply LinearMap.ext
      intro x
      simp only [LinearMap.sum_apply, hp_apply, Module.End.one_apply]
      rw [← Finset.mul_sum, he.complete, mul_one]
  let : ∀ i, Module.Finite R (p i).range := fun i =>
    Module.Finite.of_surjective (p i).rangeRestrict (p i).surjective_rangeRestrict
  have hsplit (i : ι) :
      (p i).rangeRestrict.comp (p i).range.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact ((LinearMap.isProj_range_iff_isIdempotentElem (p i)).mpr (hp.idem i)).map_id
      x x.property
  let : ∀ i, Module.Projective R (p i).range := fun i =>
    Module.Projective.of_split (p i).range.subtype (p i).rangeRestrict (hsplit i)
  let : ∀ i, IsLocalRing (End (F i)) := h
  let : ∀ i, IsLocalRing (he.idem i).Corner := fun i =>
    (biproduct.endCornerRingEquiv F i).isLocalRing
  let : ∀ i, IsLocalRing (Module.End R (p i).range) := fun i =>
    (he.idem i).isLocalRing_end_range_mulRight
  let : IsSemisimpleRing (R ⧸ Ring.jacobson R) :=
    Ring.isSemisimpleRing_quotient_jacobson_of_linearEquiv_pi hp.linearEquivPiRange
  exact Bass.stableRangeCondition_one_of_isSemisimpleRing_quotient_jacobson
    (R := End (biproduct F))

/-- Every retract of a finite biproduct of objects with local endomorphism
rings has an endomorphism ring satisfying Bass's stable range condition in
degree one. The index, object and morphism universes are independent. -/
theorem stableRangeCondition_one_end_of_retract_biproduct
    {C : Type u} [Category.{v} C] [Preadditive C]
    {ι : Type w} [Finite ι] (F : ι → C) [HasBiproduct F]
    {X : C} (i : X ⟶ biproduct F) (p : biproduct F ⟶ X)
    (hip : i ≫ p = 𝟙 X) (h : ∀ j, IsLocalRing (End (F j))) :
    Bass.StableRangeCondition (End X) 1 := by
  exact stableRangeCondition_one_end_of_retract i p hip
    (stableRangeCondition_one_end_biproduct F h)

end CategoryTheory
