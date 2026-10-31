/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Regular
public import StableRange.Local
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.Mat

/-!
# Biproduct cancellation from stable range one

An object whose canonical endomorphism ring satisfies Bass's right
stable-range-one condition cancels from a binary biproduct. In particular,
an object with a local endomorphism ring has this cancellation property.
Only the two displayed biproducts are required; the remaining objects are
unrestricted, and the endomorphism ring need not be commutative.

The conclusion asserts existence of an isomorphism, not a canonical choice.
This is the preadditive-category counterpart of the module cancellation
statement in `StableRange.Cancellation`.

## References

* `StableRange.Cancellation`, for the prior module cancellation formalization
  generalized here. Its inherited bibliographic context is C. A. Weibel,
  *The K-book*, Exercise I.1.13(c), on unit-regular cancellation; the `(S₁)`
  argument uses the existing unit-valued pair-shortening theorem.
* [Homological Algebra](https://github.com/FormalFrontier/homological-algebra),
  `HomologicalAlgebra.Preadditive.BiproductUniqueness`, for the additive-envelope
  transport, canonical End ring comparison and fully faithful reflection pattern.
* Mathlib, `CategoryTheory.Preadditive.Biproducts` and
  `CategoryTheory.Preadditive.Mat`, for Kim Morrison's categorical Gaussian
  elimination and additive-envelope implementations.

## Implementation notes

The pivot adjustment follows the existing module proof. The Gaussian step
uses Mathlib's `Biprod.isoElim` in the additive envelope `Mat_ C`; the fully
faithful additive embedding preserves the two supplied biproducts and reflects
the resulting complement isomorphism. Thus no global sum hypothesis is needed
in the original category.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

private theorem nonempty_iso_of_biprod_iso_of_end_stableRangeCondition_one_aux
    [HasBinaryBiproducts C] (X Y Z : C)
    (hX : Bass.StableRangeCondition (End X) 1) (e : (X ⊞ Y) ≅ (X ⊞ Z)) :
    Nonempty (Y ≅ Z) := by
  let a : End X := biprod.inl ≫ e.hom ≫ biprod.fst
  let c : Y ⟶ X := biprod.inr ≫ e.hom ≫ biprod.fst
  let p : End X := biprod.inl ≫ e.inv ≫ biprod.fst
  let q : X ⟶ Y := biprod.inl ≫ e.inv ≫ biprod.snd
  have hblocks : p ≫ a + q ≫ c = 𝟙 X := by
    calc
      p ≫ a + q ≫ c =
          biprod.inl ≫ e.inv ≫
            (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫
            e.hom ≫ biprod.fst := by
              simp only [a, c, p, q, Preadditive.comp_add, Preadditive.add_comp,
                Category.assoc]
      _ = 𝟙 X := by rw [biprod.total]; simp
  -- In canonical End multiplication, `a * p = p ≫ a`.
  let k : End X := q ≫ c
  have hpair : ∃ s w : End X, k * s + a * w = 1 := by
    refine ⟨1, p, ?_⟩
    simpa only [End.mul_def, End.one_def, Category.id_comp, k, add_comm] using hblocks
  obtain ⟨t, ht⟩ :=
    Bass.stableRangeCondition_one_iff_forall_isUnit_sub_mul.mp hX k a hpair
  let e' := Biprod.unipotentUpper (-(t ≫ q)) ≪≫ e
  have hpivot : biprod.inl ≫ e'.hom ≫ biprod.fst = a - k * t := by
    calc
      _ = (biprod.inl ≫ (Biprod.unipotentUpper (-(t ≫ q))).hom) ≫
          e.hom ≫ biprod.fst := by simp only [e', Iso.trans_hom, Category.assoc]
      _ = a - k * t := by
        simp [Biprod.unipotentUpper, a, k, c, End.mul_def,
          Preadditive.add_comp, Category.assoc, sub_eq_add_neg]
  have : IsIso (biprod.inl ≫ e'.hom ≫ biprod.fst) := by
    rw [hpivot]
    exact (isUnit_iff_isIso _).mp ht
  exact ⟨Biprod.isoElim e'⟩

/-- An object whose endomorphism ring satisfies `(S₁)` cancels from a binary
biproduct. Only the two displayed biproducts are needed, with no further
hypotheses on the remaining objects. This generalizes the prior module
cancellation formalization in `StableRange.Cancellation` using unit-valued
pair shortening and categorical Gaussian elimination. The inherited reference
Weibel, *The K-book*, Exercise I.1.13(c), supplies unit-regular cancellation
context; the `(S₁)` hypothesis here is more general. -/
theorem nonempty_iso_of_biprod_iso_of_end_stableRangeCondition_one
    (X Y Z : C) [HasBinaryBiproduct X Y] [HasBinaryBiproduct X Z]
    (hX : Bass.StableRangeCondition (End X) 1) (e : (X ⊞ Y) ≅ (X ⊞ Z)) :
    Nonempty (Y ≅ Z) := by
  let E := Mat_.embedding C
  let hf := Functor.FullyFaithful.ofFullyFaithful E
  let θ : End X ≃+* End (E.obj X) :=
    MulEquiv.toRingEquiv (hf.mulEquivEnd X) (fun _ _ => E.map_add)
  let : HasBinaryBiproducts (Mat_ C) := hasBinaryBiproducts_of_finite_biproducts _
  let : PreservesBinaryBiproducts E :=
    preservesBinaryBiproducts_of_preservesBiproducts E
  obtain ⟨f⟩ := nonempty_iso_of_biprod_iso_of_end_stableRangeCondition_one_aux
    (E.obj X) (E.obj Y) (E.obj Z) (hX.map_equiv θ)
    ((E.mapBiprod X Y).symm ≪≫ E.mapIso e ≪≫ E.mapBiprod X Z)
  exact ⟨hf.preimageIso f⟩

/-- An object with a possibly noncommutative local endomorphism ring cancels
from a binary biproduct, without conditions on the remaining objects. -/
theorem nonempty_iso_of_biprod_iso_of_isLocalRing_end
    (X Y Z : C) [HasBinaryBiproduct X Y] [HasBinaryBiproduct X Z]
    [IsLocalRing (End X)] (e : (X ⊞ Y) ≅ (X ⊞ Z)) :
    Nonempty (Y ≅ Z) :=
  nonempty_iso_of_biprod_iso_of_end_stableRangeCondition_one X Y Z
    Bass.stableRangeCondition_one_of_isLocalRing e

end CategoryTheory
