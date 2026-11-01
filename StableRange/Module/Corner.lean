/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Equivalences of idempotent corners

An idempotent corner is preserved by a ring equivalence and commutes with taking
multiplicative opposites. The corner of an idempotent module endomorphism is the
endomorphism semiring of its range.

The endomorphism equivalence uses the inclusion `j : e.range →ₗ[R] M` and the
corestriction `q = e.rangeRestrict`. They satisfy `j.comp q = e` and
`q.comp j = LinearMap.id`. Its forward map restricts an endomorphism to the range;
its inverse sends `f` to `j.comp (f.comp q)`. Multiplication is ordinary composition,
so `(g * h) x = g (h x)` throughout.

The ambient value of an element `x` of the canonical corner is accessed by `x.1`.
No nonzero or nontriviality assumption is needed for these equivalences. The final
locality consequence uses the existing transport of `IsLocalRing` along a ring
equivalence and its existing opposite instance; that premise itself excludes a
subsingleton corner.
-/

@[expose] public section

universe u v

open MulOpposite

namespace IsIdempotentElem

section Mul

variable {R : Type u} [Mul R] {e : R}

/-- An idempotent remains idempotent in the multiplicative opposite. -/
theorem op (he : IsIdempotentElem e) : IsIdempotentElem (MulOpposite.op e) :=
  congrArg MulOpposite.op (show e * e = e from he)

end Mul

section Semigroup

variable {R : Type u} [Semigroup R] {e : R} (he : IsIdempotentElem e)

/-- Left multiplication by the idempotent fixes every element of its corner. -/
@[simp] theorem corner_mul_left (x : he.Corner) : e * x.1 = x.1 :=
  ((Subsemigroup.mem_corner_iff he).mp x.2).1

/-- Right multiplication by the idempotent fixes every element of its corner. -/
@[simp] theorem corner_mul_right (x : he.Corner) : x.1 * e = x.1 :=
  ((Subsemigroup.mem_corner_iff he).mp x.2).2

end Semigroup

section NonUnitalSemiring

variable {R : Type u} {S : Type v} [NonUnitalSemiring R] [NonUnitalSemiring S]
variable {e : R} (he : IsIdempotentElem e)

/-- The unit of an idempotent corner has ambient value the idempotent. -/
@[simp] theorem val_corner_one : (1 : he.Corner).1 = e := rfl

/-- A ring equivalence restricts to an equivalence of the corresponding corners. -/
def cornerCongr (f : R ≃+* S) : he.Corner ≃+* (IsIdempotentElem.map he f).Corner where
  toFun x := ⟨f x.1, (Subsemigroup.mem_corner_iff (IsIdempotentElem.map he f)).mpr ⟨by
    calc
      f e * f x.1 = f (e * x.1) := (f.map_mul _ _).symm
      _ = f x.1 := congrArg f (corner_mul_left he x), by
    calc
      f x.1 * f e = f (x.1 * e) := (f.map_mul _ _).symm
      _ = f x.1 := congrArg f (corner_mul_right he x)⟩⟩
  invFun y := ⟨f.symm y.1, (Subsemigroup.mem_corner_iff he).mpr ⟨by
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using
      ((Subsemigroup.mem_corner_iff (IsIdempotentElem.map he f)).mp y.2).1, by
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using
      ((Subsemigroup.mem_corner_iff (IsIdempotentElem.map he f)).mp y.2).2⟩⟩
  left_inv x := Subtype.ext (f.symm_apply_apply x.1)
  right_inv y := Subtype.ext (f.apply_symm_apply y.1)
  map_add' x y := Subtype.ext (f.map_add x.1 y.1)
  map_mul' x y := Subtype.ext (f.map_mul x.1 y.1)

@[simp] theorem cornerCongr_apply (f : R ≃+* S) (x : he.Corner) :
    (cornerCongr he f x).1 = f x.1 := rfl

@[simp] theorem cornerCongr_symm_apply (f : R ≃+* S)
    (y : (IsIdempotentElem.map he f).Corner) :
    ((cornerCongr he f).symm y).1 = f.symm y.1 := rfl

theorem cornerCongr_one (f : R ≃+* S) :
    (cornerCongr he f 1).1 = f e := rfl

/-- The opposite of a corner is the corner of the opposite idempotent.
The two support equations exchange places, as does the order of multiplication. -/
def cornerOpEquiv : he.Cornerᵐᵒᵖ ≃+* (IsIdempotentElem.op he).Corner where
  toFun x := ⟨MulOpposite.op (unop x).1,
    (Subsemigroup.mem_corner_iff (IsIdempotentElem.op he)).mpr
      ⟨congrArg MulOpposite.op (corner_mul_right he (unop x)),
       congrArg MulOpposite.op (corner_mul_left he (unop x))⟩⟩
  invFun y := MulOpposite.op ⟨unop y.1,
    (Subsemigroup.mem_corner_iff he).mpr
      ⟨congrArg unop
          (((Subsemigroup.mem_corner_iff (IsIdempotentElem.op he)).mp y.2).2),
       congrArg unop
          (((Subsemigroup.mem_corner_iff (IsIdempotentElem.op he)).mp y.2).1)⟩⟩
  left_inv _ := MulOpposite.unop_injective (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

@[simp] theorem cornerOpEquiv_apply (x : he.Cornerᵐᵒᵖ) :
    (cornerOpEquiv he x).1 = MulOpposite.op (unop x).1 := rfl

@[simp] theorem cornerOpEquiv_symm_apply (y : (IsIdempotentElem.op he).Corner) :
    (unop ((cornerOpEquiv he).symm y)).1 = unop y.1 := rfl

theorem cornerOpEquiv_one :
    (cornerOpEquiv he 1).1 = MulOpposite.op e := rfl

end NonUnitalSemiring

section Module

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
variable {e : Module.End R M} (he : IsIdempotentElem e)

/-- The corner of an idempotent endomorphism is the endomorphism semiring of its range.
The forward map is restriction, and the inverse extends along the projection `e`. -/
def cornerEquivEnd : he.Corner ≃+* Module.End R e.range where
  toFun g := g.1.restrict fun x _ =>
    ((LinearMap.isProj_range_iff_isIdempotentElem e).mpr he).mem_iff_map_id.mpr
      (congrArg (fun k : Module.End R M => k x) (corner_mul_left he g))
  invFun f := ⟨e.range.subtype.comp (f.comp e.rangeRestrict), by
    apply (Subsemigroup.mem_corner_iff he).mpr
    constructor
    · apply LinearMap.ext
      intro x
      exact ((LinearMap.isProj_range_iff_isIdempotentElem e).mpr he).map_id
        (f (e.rangeRestrict x)) (f (e.rangeRestrict x)).2
    · apply LinearMap.ext
      intro x
      have hx : e.rangeRestrict (e x) = e.rangeRestrict x :=
        Subtype.ext (congrArg (fun k : Module.End R M => k x) (show e * e = e from he))
      exact congrArg (fun y : e.range => (f y : M)) hx⟩
  left_inv g := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun k : Module.End R M => k x) (corner_mul_right he g)
  right_inv f := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hx : e.rangeRestrict (x : M) = x :=
      Subtype.ext (((LinearMap.isProj_range_iff_isIdempotentElem e).mpr he).map_id x x.2)
    exact congrArg (fun y : e.range => (f y : M)) hx
  map_add' g h := by
    apply LinearMap.ext
    intro x
    exact Subtype.ext rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    exact Subtype.ext rfl

@[simp] theorem cornerEquivEnd_apply (g : he.Corner) (x : e.range) :
    (cornerEquivEnd he g x : M) = g.1 x := rfl

/-- Extension to the ambient module is inclusion composed with `f` and range corestriction. -/
theorem val_cornerEquivEnd_symm (f : Module.End R e.range) :
    ((cornerEquivEnd he).symm f).1 =
      e.range.subtype.comp (f.comp e.rangeRestrict) := rfl

@[simp] theorem cornerEquivEnd_symm_apply (f : Module.End R e.range) (x : M) :
    ((cornerEquivEnd he).symm f).1 x = (f (e.rangeRestrict x) : M) := rfl

/-- The inverse equivalence sends the identity of the range to the original projection. -/
theorem val_cornerEquivEnd_symm_one :
    ((cornerEquivEnd he).symm 1).1 = e := by
  rw [map_one]
  exact val_corner_one he

end Module

section RegularModule

variable {R : Type u} [Semiring R] {e : R} (he : IsIdempotentElem e)

/-- If the corner of an idempotent is local, the endomorphism semiring of its
principal left ideal is local. The ideal is realized as the range of right
multiplication on the canonical left regular module. -/
theorem isLocalRing_end_range_mulRight [IsLocalRing he.Corner] :
    IsLocalRing (Module.End R (RingEquiv.moduleEndSelf R (MulOpposite.op e)).range) := by
  exact (((cornerOpEquiv he).trans
    (cornerCongr (IsIdempotentElem.op he) (RingEquiv.moduleEndSelf R))).trans
    (cornerEquivEnd (IsIdempotentElem.map (IsIdempotentElem.op he)
      (RingEquiv.moduleEndSelf R)))).isLocalRing

end RegularModule

end IsIdempotentElem
