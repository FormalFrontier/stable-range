/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Regular
public import Mathlib.RingTheory.Idempotents
import Mathlib.Tactic.NoncommRing

/-!
# Stable range one in idempotent corners

An idempotent corner inherits Bass's stable-range-one condition from its ambient ring.
The identity in the corner is the idempotent, even when the idempotent is not central.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Exercise I.1.5 (the stable-range condition used here).
* Mathlib, `RingTheory.Idempotents` (the formalization of idempotent corners).
-/

set_option warningAsError true

@[expose] public section

namespace Bass

universe u

/-- Stable range one passes to the corner of any idempotent in a ring.
The corner formalization is from Mathlib's `RingTheory.Idempotents`; the
stable-range condition is as in Weibel, *The K-book*, Exercise I.1.5. -/
theorem stableRangeCondition_one_corner
    {R : Type u} [Ring R] {e : R} (he : IsIdempotentElem e)
    (h : StableRangeCondition R 1) : StableRangeCondition he.Corner 1 := by
  apply stableRangeCondition_one_iff_forall_isUnit_sub_mul.mpr
  intro a b ⟨x, y, hxy⟩
  let cornerVal (z : he.Corner) : R := ((show Subsemigroup.corner e from z) : R)
  have corner_mem (z : he.Corner) :
      e * cornerVal z = cornerVal z ∧ cornerVal z * e = cornerVal z :=
    (Subsemigroup.mem_corner_iff he).mp z.property
  let q : R := 1 - e
  have hq_sq : q * q = q := by dsimp [q]; noncomm_ring [he.eq]
  have hq_e : q * e = 0 := by dsimp [q]; noncomm_ring [he.eq]
  have he_plus_q : e + q = 1 := by dsimp [q]; abel
  have q_corner (z : he.Corner) :
      q * cornerVal z = 0 ∧ cornerVal z * q = 0 := by
    obtain ⟨hz_left, hz_right⟩ := corner_mem z
    constructor <;> dsimp [q] <;> noncomm_ring [hz_left, hz_right]
  have hxyR : cornerVal a * cornerVal x + cornerVal b * cornerVal y = e := by
    have heq := congrArg cornerVal hxy
    change cornerVal a * cornerVal x + cornerVal b * cornerVal y = e at heq
    exact heq
  have hpair : cornerVal a * cornerVal x +
      (cornerVal b + q) * (cornerVal y + q) = 1 := by
    calc
      cornerVal a * cornerVal x + (cornerVal b + q) * (cornerVal y + q) =
          cornerVal a * cornerVal x + cornerVal b * cornerVal y + q := by
            noncomm_ring [(q_corner b).2, (q_corner y).1, hq_sq]
      _ = 1 := by rw [hxyR, he_plus_q]
  obtain ⟨t, hunit⟩ := (stableRangeCondition_one_iff_forall_isUnit_sub_mul.mp h)
    (cornerVal a) (cornerVal b + q)
    ⟨cornerVal x, cornerVal y + q, hpair⟩
  let ambientUnit : R := cornerVal b + q - cornerVal a * t
  have hq_mul_at : q * (cornerVal a * t) = 0 := by
    rw [← mul_assoc, (q_corner a).1, zero_mul]
  have hqu : q * ambientUnit = q := by
    dsimp [ambientUnit]
    noncomm_ring [(q_corner b).1, hq_sq, hq_mul_at]
  obtain ⟨inverse, hright, hleft⟩ :=
    isUnit_iff_exists.mp (show IsUnit ambientUnit from hunit)
  have hq_inverse : q * inverse = q := by
    calc
      q * inverse = (q * ambientUnit) * inverse := by rw [hqu]
      _ = q * (ambientUnit * inverse) := by rw [mul_assoc]
      _ = q := by rw [hright, mul_one]
  let compress (r : R) : he.Corner := ⟨e * r * e, ⟨r, rfl⟩⟩
  have hone_minus_q : 1 - q = e := by dsimp [q]; abel
  have compress_mul (r s : R) :
      (e * r * e) * (e * s * e) = e * r * e * s * e := by
    calc
      (e * r * e) * (e * s * e) = e * r * (e * e) * s * e := by noncomm_ring
      _ = e * r * e * s * e := by rw [he.eq]
  have hcompressed_right : (e * ambientUnit * e) * (e * inverse * e) = e := by
    calc
      (e * ambientUnit * e) * (e * inverse * e) =
          e * ambientUnit * (1 - q) * inverse * e := by
            rw [compress_mul, hone_minus_q]
      _ = e * (ambientUnit * inverse) * e -
          e * ambientUnit * (q * inverse) * e := by noncomm_ring
      _ = e := by rw [hright, hq_inverse]; noncomm_ring [he.eq, hq_e]
  have hcompressed_left : (e * inverse * e) * (e * ambientUnit * e) = e := by
    calc
      (e * inverse * e) * (e * ambientUnit * e) =
          e * inverse * (1 - q) * ambientUnit * e := by
            rw [compress_mul, hone_minus_q]
      _ = e * (inverse * ambientUnit) * e -
          e * inverse * (q * ambientUnit) * e := by noncomm_ring
      _ = e := by rw [hleft, hqu]; noncomm_ring [he.eq, hq_e]
  have hcorner_unit : IsUnit (compress ambientUnit) := by
    apply isUnit_iff_exists.mpr
    refine ⟨compress inverse, ?_, ?_⟩
    · apply Subtype.ext
      change (e * ambientUnit * e) * (e * inverse * e) = e
      exact hcompressed_right
    · apply Subtype.ext
      change (e * inverse * e) * (e * ambientUnit * e) = e
      exact hcompressed_left
  have hcorner_eq : b - a * compress t = compress ambientUnit := by
    apply Subtype.ext
    change cornerVal b - cornerVal a * (e * t * e) = e * ambientUnit * e
    dsimp [ambientUnit, q]
    noncomm_ring [he.eq, (corner_mem a).1, (corner_mem a).2,
      (corner_mem b).1, (corner_mem b).2];
      simp only [← mul_assoc (cornerVal a) e, (corner_mem a).2,
        ← mul_assoc e (cornerVal a), (corner_mem a).1]
  exact ⟨compress t, hcorner_eq ▸ hcorner_unit⟩

end Bass
