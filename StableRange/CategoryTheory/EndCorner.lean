/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.Idempotents

/-!
# Corners of retract and biproduct endomorphism rings

A displayed retraction determines an idempotent whose canonical unital corner
is ring-equivalent to the endomorphism ring of the retract. No complementary
object or idempotent-completeness hypothesis is needed.

Each summand of a biproduct determines an idempotent in the canonical endomorphism
ring of the biproduct. Its unital corner is ring-equivalent to the canonical
endomorphism ring of the summand. Multiplication in both endomorphism rings is
reverse categorical composition; no centrality of the idempotent is assumed.

The corner equivalence needs only the displayed biproduct, with an arbitrary
index type. For a finite index type equipped with `Fintype`, the same idempotents
form a complete orthogonal family. The index universe is independent of the
object and morphism universes.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {X Z : C}

/-- The projection and inclusion of a retract determine an idempotent on the
ambient object. -/
theorem isIdempotentElem_comp_of_retract
    (i : X ⟶ Z) (p : Z ⟶ X) (h : i ≫ p = 𝟙 X) :
    IsIdempotentElem (M := End Z) (p ≫ i) := by
  change (p ≫ i) ≫ (p ≫ i) = p ≫ i
  simp only [Category.assoc]
  rw [← Category.assoc i p i, h, Category.id_comp]

variable [Preadditive C]

/-- The endomorphism ring of a retract is the canonical unital corner cut out by
its projection and inclusion. The corner unit is `p ≫ i`, not `𝟙 Z`. -/
noncomputable def endCornerRingEquivOfRetract
    (i : X ⟶ Z) (p : Z ⟶ X) (h : i ≫ p = 𝟙 X) :
    End X ≃+* (isIdempotentElem_comp_of_retract i p h).Corner where
  toFun a := ⟨p ≫ a ≫ i,
    (Subsemigroup.mem_corner_iff (isIdempotentElem_comp_of_retract i p h)).mpr
      ⟨by
          simp only [End.mul_def, Category.assoc]
          rw [← Category.assoc i p i, h, Category.id_comp],
        by
          simp only [End.mul_def, Category.assoc]
          rw [← Category.assoc i p (a ≫ i), h, Category.id_comp]⟩⟩
  invFun c := i ≫ c.1 ≫ p
  left_inv a := by
    change i ≫ (p ≫ a ≫ i) ≫ p = a
    simp only [Category.assoc]
    rw [← Category.assoc i p (a ≫ i ≫ p)]
    simp only [h, Category.id_comp, Category.comp_id]
  right_inv c := by
    apply Subtype.ext
    change p ≫ (i ≫ c.1 ≫ p) ≫ i = c.1
    have hc : c.1 ≫ (p ≫ i) = c.1 ∧ (p ≫ i) ≫ c.1 = c.1 :=
      (Subsemigroup.mem_corner_iff (isIdempotentElem_comp_of_retract i p h)).mp c.2
    calc
      _ = (p ≫ i) ≫ c.1 ≫ (p ≫ i) := by simp only [Category.assoc]
      _ = c.1 := by rw [hc.1, hc.2]
  map_mul' a b := by
    apply Subtype.ext
    change p ≫ (b ≫ a) ≫ i = (p ≫ b ≫ i) ≫ (p ≫ a ≫ i)
    simp only [Category.assoc]
    rw [← Category.assoc i p (a ≫ i), h, Category.id_comp]
  map_add' a b := by
    apply Subtype.ext
    change p ≫ (a + b) ≫ i = (p ≫ a ≫ i) + (p ≫ b ≫ i)
    calc
      p ≫ (a + b) ≫ i = p ≫ (a ≫ i + b ≫ i) :=
        congrArg (fun f : X ⟶ Z => p ≫ f)
          (Preadditive.add_comp X X Z a b i)
      _ = (p ≫ a ≫ i) + (p ≫ b ≫ i) :=
        Preadditive.comp_add Z X Z p (a ≫ i) (b ≫ i)

/-- The corner equivalence extends an endomorphism through the projection and
inclusion of the retract. -/
@[simp]
theorem val_endCornerRingEquivOfRetract_apply
    (i : X ⟶ Z) (p : Z ⟶ X) (h : i ≫ p = 𝟙 X) (a : End X) :
    (endCornerRingEquivOfRetract i p h a).1 = p ≫ a ≫ i := rfl

/-- The inverse corner equivalence restricts a supported endomorphism to the
retract. -/
@[simp]
theorem endCornerRingEquivOfRetract_symm_apply
    (i : X ⟶ Z) (p : Z ⟶ X) (h : i ≫ p = 𝟙 X)
    (a : (isIdempotentElem_comp_of_retract i p h).Corner) :
    (endCornerRingEquivOfRetract i p h).symm a = i ≫ a.1 ≫ p := rfl

end CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {I : Type w} (F : I → C) [HasBiproduct F]

/-- Projection onto a biproduct summand followed by its inclusion is idempotent
in the canonical endomorphism ring of the biproduct. -/
theorem biproduct.isIdempotentElem_π_ι (i : I) :
    IsIdempotentElem (M := End (biproduct F))
      (biproduct.π F i ≫ biproduct.ι F i) := by
  exact isIdempotentElem_comp_of_retract (biproduct.ι F i) (biproduct.π F i)
    (by simp only [biproduct.ι_π_self])

/-- The endomorphism ring of a biproduct summand is the unital corner cut out by
its projection and inclusion. The corner unit is `biproduct.π F i ≫ biproduct.ι F i`,
not the identity endomorphism of the whole biproduct. -/
noncomputable def biproduct.endCornerRingEquiv (i : I) :
    End (F i) ≃+* (biproduct.isIdempotentElem_π_ι F i).Corner :=
  endCornerRingEquivOfRetract (biproduct.ι F i) (biproduct.π F i)
    (by simp only [biproduct.ι_π_self])

/-- The corner equivalence sends a summand endomorphism to its extension through
the corresponding projection and inclusion. -/
@[simp]
theorem biproduct.val_endCornerRingEquiv_apply (i : I) (a : End (F i)) :
    (biproduct.endCornerRingEquiv F i a).1 =
      biproduct.π F i ≫ a ≫ biproduct.ι F i := rfl

/-- The inverse corner equivalence restricts a supported endomorphism to the
corresponding summand. -/
@[simp]
theorem biproduct.endCornerRingEquiv_symm_apply (i : I)
    (c : (biproduct.isIdempotentElem_π_ι F i).Corner) :
    (biproduct.endCornerRingEquiv F i).symm c =
      biproduct.ι F i ≫ c.1 ≫ biproduct.π F i := rfl

/-- The canonical summand idempotents of a finite biproduct form a complete
orthogonal family in its canonical endomorphism ring. This includes the empty
family and does not require the index universe to be the object universe. -/
theorem biproduct.completeOrthogonalIdempotents [Fintype I] :
    CompleteOrthogonalIdempotents (R := End (biproduct F))
      (fun i => biproduct.π F i ≫ biproduct.ι F i) where
  idem := biproduct.isIdempotentElem_π_ι F
  ortho i j hij := by
    -- Multiplication reverses composition, so the middle indices are `j, i`.
    change (biproduct.π F j ≫ biproduct.ι F j) ≫
      (biproduct.π F i ≫ biproduct.ι F i) = 0
    simp only [Category.assoc, biproduct.ι_π_ne_assoc F hij.symm, zero_comp, comp_zero]
  complete := by
    change (∑ i, biproduct.π F i ≫ biproduct.ι F i) = 𝟙 (biproduct F)
    exact IsBilimit.total (biproduct.isBilimit F)

end CategoryTheory.Limits
