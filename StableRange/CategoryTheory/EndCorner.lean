/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.Idempotents

/-!
# Corners of biproduct endomorphism rings

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

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {I : Type w} (F : I → C) [HasBiproduct F]

/-- Projection onto a biproduct summand followed by its inclusion is idempotent
in the canonical endomorphism ring of the biproduct. -/
theorem biproduct.isIdempotentElem_π_ι (i : I) :
    IsIdempotentElem (M := End (biproduct F))
      (biproduct.π F i ≫ biproduct.ι F i) := by
  change (biproduct.π F i ≫ biproduct.ι F i) ≫
    (biproduct.π F i ≫ biproduct.ι F i) = biproduct.π F i ≫ biproduct.ι F i
  simp only [Category.assoc, biproduct.ι_π_self_assoc]

/-- The endomorphism ring of a biproduct summand is the unital corner cut out by
its projection and inclusion. The corner unit is `biproduct.π F i ≫ biproduct.ι F i`,
not the identity endomorphism of the whole biproduct. -/
noncomputable def biproduct.endCornerRingEquiv (i : I) :
    End (F i) ≃+* (biproduct.isIdempotentElem_π_ι F i).Corner where
  toFun a := ⟨biproduct.π F i ≫ a ≫ biproduct.ι F i,
    (Subsemigroup.mem_corner_iff (biproduct.isIdempotentElem_π_ι F i)).mpr
      ⟨by
          simp only [End.mul_def, Category.assoc, biproduct.ι_π_self_assoc],
        by
          simp only [End.mul_def, Category.assoc, biproduct.ι_π_self_assoc]⟩⟩
  invFun c := biproduct.ι F i ≫ c.1 ≫ biproduct.π F i
  left_inv a := by
    change biproduct.ι F i ≫ (biproduct.π F i ≫ a ≫ biproduct.ι F i) ≫
      biproduct.π F i = a
    simp only [Category.assoc, biproduct.ι_π_self_assoc, biproduct.ι_π_self,
      Category.comp_id]
  right_inv c := by
    apply Subtype.ext
    change biproduct.π F i ≫ (biproduct.ι F i ≫ c.1 ≫ biproduct.π F i) ≫
      biproduct.ι F i = c.1
    have hc :
        c.1 ≫ (biproduct.π F i ≫ biproduct.ι F i) = c.1 ∧
          (biproduct.π F i ≫ biproduct.ι F i) ≫ c.1 = c.1 :=
      (Subsemigroup.mem_corner_iff (biproduct.isIdempotentElem_π_ι F i)).mp c.2
    calc
      _ = (biproduct.π F i ≫ biproduct.ι F i) ≫ c.1 ≫
          (biproduct.π F i ≫ biproduct.ι F i) := by simp only [Category.assoc]
      _ = c.1 := by rw [hc.1, hc.2]
  map_mul' a b := by
    apply Subtype.ext
    change biproduct.π F i ≫ (b ≫ a) ≫ biproduct.ι F i =
      (biproduct.π F i ≫ b ≫ biproduct.ι F i) ≫
        (biproduct.π F i ≫ a ≫ biproduct.ι F i)
    simp only [Category.assoc, biproduct.ι_π_self_assoc]
  map_add' a b := by
    apply Subtype.ext
    change biproduct.π F i ≫ (a + b) ≫ biproduct.ι F i =
      (biproduct.π F i ≫ a ≫ biproduct.ι F i) +
        (biproduct.π F i ≫ b ≫ biproduct.ι F i)
    calc
      biproduct.π F i ≫ (a + b) ≫ biproduct.ι F i =
          biproduct.π F i ≫ (a ≫ biproduct.ι F i + b ≫ biproduct.ι F i) :=
        congrArg (fun f : F i ⟶ biproduct F => biproduct.π F i ≫ f)
          (Preadditive.add_comp (F i) (F i) (biproduct F) a b (biproduct.ι F i))
      _ = (biproduct.π F i ≫ a ≫ biproduct.ι F i) +
          (biproduct.π F i ≫ b ≫ biproduct.ι F i) :=
        Preadditive.comp_add (biproduct F) (F i) (biproduct F)
          (biproduct.π F i) (a ≫ biproduct.ι F i) (b ≫ biproduct.ι F i)

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
