/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Commutative
public import StableRange.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import StableRange.Local

/-!
# Stable range one for zero-dimensional commutative rings

This file proves that every commutative ring of Krull dimension at most zero
satisfies Bass's condition `(S₁)`. It also packages least stable range one
for nontrivial rings and proves that commutative von Neumann-regular rings are
unit-regular.

The zero-dimensional result does not assume that the ring is reduced. Its
proof passes to the reduced quotient by the Jacobson radical, uses
commutative von Neumann regularity there, and lifts `(S₁)` through the
quasi-regular radical.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Exercise I.1.13(f) (zero-dimensional stable range and regular rings).
* Mathlib, `RingTheory.Ideal.Quotient.Nilpotent` and the commutative
  Krull-dimension and regularity APIs; `general-linear-groups`,
  `QuasiregularIdeal`, for the radical quotient criterion.
-/

set_option warningAsError true

@[expose] public section

namespace Bass

universe u

variable {R : Type u} [CommRing R]

/-- A commutative von Neumann-regular ring is unit-regular.

Starting from an inner inverse `x` of `a`, the reflexive inner inverse
`y = x * a * x` makes `a * y` idempotent. The element
`y + (1 - a * y)` is then a unit, with inverse `a + (1 - a * y)`.
See Weibel, *The K-book*, Exercise I.1.13(f). -/
theorem IsVonNeumannRegular.isUnitRegular
    (hreg : IsVonNeumannRegular R) : IsUnitRegular R := by
  intro a
  obtain ⟨x, hx⟩ := hreg a
  let y : R := x * a * x
  have hay : a = a * y * a := by
    dsimp only [y]
    calc
      a = a * x * a := hx
      _ = (a * x * a) * x * a := congrArg (fun z ↦ z * x * a) hx
      _ = a * (x * a * x) * a := by ring
  have hya : y = y * a * y := by
    dsimp only [y]
    calc
      x * a * x = a * x ^ 2 := by ring
      _ = (a * x * a) * x ^ 2 := congrArg (fun z ↦ z * x ^ 2) hx
      _ = a ^ 2 * x ^ 3 := by ring
      _ = a * a * x ^ 3 := by ring
      _ = (a * x * a) * a * x ^ 3 :=
        congrArg (fun z ↦ z * a * x ^ 3) hx
      _ = (x * a * x) * a * (x * a * x) := by ring
  let e : R := a * y
  have he : e * e = e := by
    dsimp only [e]
    calc
      (a * y) * (a * y) = (a * y * a) * y := by ring
      _ = a * y := by rw [← hay]
  have haComp : a * (1 - e) = 0 := by
    dsimp only [e]
    rw [mul_sub, mul_one]
    calc
      a - a * (a * y) = a - a * y * a := by ring
      _ = 0 := by rw [← hay, sub_self]
  have hyComp : y * (1 - e) = 0 := by
    dsimp only [e]
    rw [mul_sub, mul_one]
    calc
      y - y * (a * y) = y - y * a * y := by ring
      _ = 0 := by rw [← hya, sub_self]
  have hyaE : y * a = e := by simp only [e, mul_comm]
  have hCompA : (1 - e) * a = 0 := by simpa only [mul_comm] using haComp
  have huv : (y + (1 - e)) * (a + (1 - e)) = 1 := by
    calc
      (y + (1 - e)) * (a + (1 - e)) =
          y * a + y * (1 - e) + (1 - e) * a +
            (1 - e) * (1 - e) := by ring
      _ = e + (1 - e) * (1 - e) := by
        rw [hyaE, hyComp, hCompA]
        simp
      _ = e + (1 - 2 * e + e * e) := by ring
      _ = 1 := by rw [he]; ring
  let unit : Rˣ :=
    ⟨y + (1 - e), a + (1 - e), huv,
      by simpa only [mul_comm] using huv⟩
  refine ⟨unit, ?_⟩
  change a = a * (y + (1 - e)) * a
  rw [mul_add, add_mul, haComp, zero_mul]
  simpa only [add_zero] using hay

/-- Every zero-dimensional commutative ring satisfies Bass's condition
`(S₁)`. No reducedness or nontriviality hypothesis is needed; compare Weibel,
*The K-book*, Exercise I.1.13(f), where the nonzero-ring convention applies. -/
theorem stableRangeCondition_one_of_krullDimLE_zero
    [Ring.KrullDimLE 0 R] : StableRangeCondition R 1 := by
  let J : TwoSidedIdeal R := (Ring.jacobson R).toTwoSided
  have hJ : J.asIdeal = Ring.jacobson R := by
    simpa only [J] using Ideal.asIdeal_toTwoSided (Ring.jacobson R)
  have hred : IsReduced (R ⧸ J.asIdeal) := by
    apply (Ideal.isRadical_iff_quotient_reduced J.asIdeal).mp
    rw [hJ, Ring.jacobson_eq_nilradical_of_krullDimLE_zero R]
    exact Ideal.radical_isRadical ⊥
  have hdim : Ring.KrullDimLE 0 (R ⧸ J.asIdeal) := by
    rw [Ring.krullDimLE_iff]
    exact (ringKrullDim_quotient_le J.asIdeal).trans
      (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 0 R))
  let _ : IsReduced (R ⧸ J.asIdeal) := hred
  let _ : Ring.KrullDimLE 0 (R ⧸ J.asIdeal) := hdim
  have hreg : IsVonNeumannRegular (R ⧸ J.asIdeal) :=
    isVonNeumannRegular_of_isReduced_krullDimLE_zero
  have hquot : StableRangeCondition (R ⧸ J.asIdeal) 1 :=
    hreg.isUnitRegular.stableRangeCondition_one
  exact (stableRangeCondition_quotient_iff J
    TwoSidedIdeal.ringJacobson_isQuasiregular 1).mpr hquot

/-- Every nontrivial zero-dimensional commutative ring has least Bass stable
range one; see Weibel, *The K-book*, Exercise I.1.13(f). -/
theorem stableRange_one_of_krullDimLE_zero
    [Nontrivial R] [Ring.KrullDimLE 0 R] : IsStableRange R 1 := by
  refine ⟨stableRangeCondition_one_of_krullDimLE_zero, ?_⟩
  intro n hn
  cases n with
  | zero => exact (not_stableRangeCondition_zero hn).elim
  | succ n => exact Nat.succ_le_succ (Nat.zero_le n)

end Bass
