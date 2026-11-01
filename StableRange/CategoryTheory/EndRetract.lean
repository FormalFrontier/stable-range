/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import StableRange.Module.Corner

public import StableRange.Basic
public import StableRange.CategoryTheory.EndCorner

/-!
# Stable range for endomorphism rings of retracts

Bass's stable range condition in degree one descends from the endomorphism ring
of an object to that of any displayed retract. The statement uses the original
endomorphism rings, with multiplication given by reverse categorical composition.
No complementary object, finite-length condition, or nonzero hypothesis is needed.
-/

@[expose] public section

universe u v

namespace CategoryTheory

/-- Stable range one of an endomorphism ring descends along a displayed
retraction in a preadditive category. -/
theorem stableRangeCondition_one_end_of_retract
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Z : C} (i : X ⟶ Z) (p : Z ⟶ X) (h : i ≫ p = 𝟙 X)
    (hZ : Bass.StableRangeCondition (End Z) 1) :
    Bass.StableRangeCondition (End X) 1 := by
  let e : End Z := p ≫ i
  let he : IsIdempotentElem e := isIdempotentElem_comp_of_retract i p h
  have hCorner : Bass.StableRangeCondition he.Corner 1 := by
    intro a r hr
    obtain ⟨x, q, hq⟩ := hr
    let b : he.Corner := r 0
    let y : he.Corner := q 0
    have hab : a * x + b * y = (1 : he.Corner) := by
      simpa [b, y] using hq
    have hab' : a.1 * x.1 + b.1 * y.1 = e :=
      congrArg Subtype.val hab
    let f : End Z := 1 - e
    have hfl (z : he.Corner) : f * z.1 = 0 := by
      dsimp only [f]
      rw [sub_mul, one_mul, he.corner_mul_left z, sub_self]
    have hfr (z : he.Corner) : z.1 * f = 0 := by
      dsimp only [f]
      rw [mul_sub, mul_one, he.corner_mul_right z, sub_self]
    have hfe : f * e = 0 := by
      dsimp only [f]
      rw [sub_mul, one_mul, show e * e = e from he, sub_self]
    have hef : e * f = 0 := by
      dsimp only [f]
      rw [mul_sub, mul_one, show e * e = e from he, sub_self]
    have hff : f * f = f := by
      calc
        f * f = f * (1 - e) := rfl
        _ = f := by rw [mul_sub, mul_one, hfe, sub_zero]
    -- Complete the corner row by the complementary idempotent in the ambient ring.
    have hamb : a.1 * x.1 + (b.1 + f) * (y.1 + f) = 1 := by
      calc
        _ = (a.1 * x.1 + b.1 * y.1) + f := by
          rw [add_mul, mul_add, mul_add, hfr b, hfl y, hff]
          simp only [add_zero, zero_add, add_assoc]
        _ = 1 := by
          rw [hab']
          dsimp only [f]
          rw [add_sub, add_sub_cancel_left]
    have hrow : Bass.IsRightUnimodularCons a.1
        (fun _ : Fin 1 => b.1 + f) :=
      ⟨x.1, fun _ => y.1 + f, by simpa using hamb⟩
    obtain ⟨t, w, hw⟩ := hZ a.1 (fun _ : Fin 1 => b.1 + f) hrow
    let c : End Z := b.1 + f - a.1 * t 0
    let z : End Z := w 0
    have hcz : c * z = 1 := by
      simpa [c, z] using hw
    have hfc : f * c = f := by
      dsimp only [c]
      rw [mul_sub, mul_add, hfl b, zero_add, hff,
        ← mul_assoc, hfl a, zero_mul, sub_zero]
    have hfz : f * z = f := by
      calc
        f * z = (f * c) * z := by rw [hfc]
        _ = f * (c * z) := mul_assoc _ _ _
        _ = f := by rw [hcz, mul_one]
    -- Only a right inverse is needed: its restriction has both corner supports.
    have hze : z * e = e * z * e := by
      have hz : f * (z * e) = 0 := by
        rw [← mul_assoc, hfz, hfe]
      dsimp only [f] at hz
      rw [sub_mul, one_mul, ← mul_assoc] at hz
      exact sub_eq_zero.mp hz
    let s : he.Corner :=
      ⟨e * t 0 * e, (Subsemigroup.mem_corner_iff he).mpr
        ⟨by simp only [← mul_assoc, show e * e = e from he],
          by simp only [mul_assoc, show e * e = e from he]⟩⟩
    let v : he.Corner :=
      ⟨e * z * e, (Subsemigroup.mem_corner_iff he).mpr
        ⟨by simp only [← mul_assoc, show e * e = e from he],
          by simp only [mul_assoc, show e * e = e from he]⟩⟩
    have has : a.1 * s.1 = a.1 * t 0 * e := by
      change a.1 * (e * t 0 * e) = a.1 * t 0 * e
      simp only [← mul_assoc, he.corner_mul_right a]
    have hece : e * c * e = b.1 - a.1 * s.1 := by
      dsimp only [c]
      rw [mul_sub, mul_add, he.corner_mul_left b, hef, add_zero,
        sub_mul, he.corner_mul_right b, ← mul_assoc e a.1 (t 0),
        he.corner_mul_left a, has]
    have hresult : (b - a * s) * v = (1 : he.Corner) := by
      apply Subtype.ext
      change (b.1 - a.1 * s.1) * v.1 = e
      calc
        _ = (e * c * e) * v.1 := by rw [hece]
        _ = e * c * v.1 := by rw [mul_assoc, he.corner_mul_left v]
        _ = e * c * (z * e) := by rw [hze]
        _ = e * (c * z) * e := by simp only [mul_assoc]
        _ = e := by rw [hcz, mul_one, show e * e = e from he]
    refine ⟨fun _ => s, fun _ => v, ?_⟩
    simpa [b] using hresult
  exact hCorner.map_equiv (endCornerRingEquivOfRetract i p h).symm

end CategoryTheory
