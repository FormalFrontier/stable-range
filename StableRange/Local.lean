/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Jacobson.Radical

import Mathlib.Algebra.Group.Units.Opposite
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Stable range and Jacobson radicals of local rings

This file treats local semirings in Mathlib's unit-theoretic sense, without a
commutativity assumption. Division semirings are local, and their additive
submonoid of nonunits is zero. For commutative local semirings, the additive
submonoid underlying the maximal ideal is the submonoid of nonunits.
Every local ring has Bass stable range one, and its Jacobson radical consists
exactly of its nonunits.

## Main declarations

* `DivisionSemiring.isLocalRing`: locality without commutativity or additive inverses.
* `IsLocalRing.nonunitsAddSubmonoid_eq_bot`: the nonunits form the zero additive
  submonoid in a division semiring.
* `IsLocalRing.maximalIdeal_toAddSubmonoid`: the additive view of Mathlib's
  maximal ideal in a commutative local semiring.
* `Bass.stableRange_one_of_isLocalRing`: least Bass stable range one for local rings.
* `IsLocalRing.mem_ringJacobson_iff`: the Jacobson radical consists of the nonunits
  in a possibly noncommutative local ring.

## Implementation notes

The division-semiring results use only the semiring operations and multiplicative
inverses; the stable-range and Jacobson-radical results require additive inverses.
The maximal ideal is used only under `CommSemiring`, whereas the additive submonoid
of nonunits also applies to noncommutative semirings. Mathlib's existing field-locality
instance and `IsLocalRing.maximalIdeal_eq_bot` remain available. The additive-view
lemma lets field clients compare the same maximal-ideal object with the submonoid
of nonunits, without comparing instance proofs or constructing a new ideal.

The interface uses Mathlib's `IsLocalRing` and `Ring.jacobson`, rather than a
separate local-ring class or ideal construction. The existing local unit
support `Bass.isUnit_of_mul_eq_one_right` derives invertibility from a right
inverse without a separate direct-finiteness hypothesis.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Exercise I.1.12(v) (the local stable-range-one consequence); the direct
  proof here instead uses Mathlib's `IsLocalRing` API.
* C. A. Weibel, *The K-book*, the local-ring discussion preceding Lemma I.2.2
  and the proof of that lemma (the local ideal is the Jacobson radical).
* Mathlib, `RingTheory.LocalRing.Basic` (local-ring unit criterion, the additive
  submonoid of nonunits, and the field-locality instance in namespace `Field`,
  generalized here to division semirings), `RingTheory.LocalRing.MaximalIdeal.Defs` and
  `RingTheory.LocalRing.MaximalIdeal.Basic` (the existing maximal ideal and its
  identification with the zero ideal over fields),
  `RingTheory.Jacobson.Radical` and `RingTheory.Jacobson.Ideal` (the canonical
  Jacobson radical, its properness and membership criterion), and
  `Algebra.Group.Units.Opposite` (units in the opposite ring).
-/

set_option warningAsError true

@[expose] public section

open scoped BigOperators

namespace DivisionSemiring

universe u

/-- Every division semiring is local in the unit-theoretic sense, generalizing
Mathlib's field-locality instance in `RingTheory.LocalRing.Basic`. -/
instance (priority := 100) isLocalRing (K : Type u) [DivisionSemiring K] : IsLocalRing K := by
  apply IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add
  intro a b hab
  by_cases ha : a = 0
  · exact Or.inr (by simpa only [ha, zero_add] using hab)
  · exact Or.inl (isUnit_iff_ne_zero.mpr ha)

end DivisionSemiring

namespace IsLocalRing

universe u

/-- The additive submonoid of nonunits in a division semiring is zero. -/
@[simp]
theorem nonunitsAddSubmonoid_eq_bot (K : Type u) [DivisionSemiring K] :
    nonunitsAddSubmonoid K = ⊥ := by
  apply AddSubmonoid.ext
  intro x
  change x ∈ nonunits K ↔ x ∈ (⊥ : AddSubmonoid K)
  simpa only [AddSubmonoid.mem_bot, isUnit_iff_ne_zero, not_not] using
    (mem_nonunits_iff (α := K) (a := x))

/-- The additive submonoid underlying the maximal ideal of a commutative local
semiring is the additive submonoid of nonunits. -/
@[simp]
theorem maximalIdeal_toAddSubmonoid (R : Type u) [CommSemiring R] [IsLocalRing R] :
    (maximalIdeal R).toAddSubmonoid = nonunitsAddSubmonoid R := by
  apply AddSubmonoid.ext
  intro x
  rw [Submodule.mem_toAddSubmonoid]
  exact mem_maximalIdeal x

end IsLocalRing

namespace Bass

universe u

variable {R : Type u} [Ring R]

/-- In a noncommutative local ring, an element with a right inverse is a unit.

The proof does not assume direct finiteness. It applies locality to the
idempotent `b * a`; if `1 - b * a` were a unit, then its product with `b`
would force `b = 0`, contradicting `a * b = 1`. -/
theorem isUnit_of_mul_eq_one_right [IsLocalRing R]
    {a b : R} (hab : a * b = 1) : IsUnit a := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (b * a) with hba | hba
  · let c : R := (↑(hba.unit⁻¹) : R) * b
    have hca : c * a = 1 := by
      calc
        c * a = (↑(hba.unit⁻¹) : R) * (b * a) := by
          simp only [c, mul_assoc]
        _ = (↑(hba.unit⁻¹) : R) * (hba.unit : R) := by
          exact congrArg (fun x : R ↦ (↑(hba.unit⁻¹) : R) * x)
            hba.unit_spec.symm
        _ = 1 := Units.inv_mul hba.unit
    have hcb : c = b := by
      calc
        c = c * 1 := by rw [mul_one]
        _ = c * (a * b) := by rw [hab]
        _ = (c * a) * b := (mul_assoc c a b).symm
        _ = b := by rw [hca, one_mul]
    exact ⟨⟨a, b, hab, hcb ▸ hca⟩, rfl⟩
  · have hzero : (1 - b * a) * b = 0 := by
      simp only [sub_mul, one_mul, mul_assoc, hab, mul_one, sub_self]
    have hb0 : b = 0 := hba.mul_right_eq_zero.mp hzero
    rw [hb0, mul_zero] at hab
    exact (zero_ne_one hab).elim

/-- In a local ring, one entry of a right-unimodular pair is a unit. -/
theorem isUnit_first_or_isUnit_second [IsLocalRing R]
    (r0 : R) (r : Fin 1 → R) (hr : IsRightUnimodularCons r0 r) :
    IsUnit r0 ∨ IsUnit (r 0) := by
  obtain ⟨s0, s, hs⟩ := hr
  have hsum : IsUnit (r0 * s0 + r 0 * s 0) := by
    have : r0 * s0 + r 0 * s 0 = 1 := by
      simpa only [Fin.sum_univ_one] using hs
    rw [this]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with h0 | h1
  · obtain ⟨u, hu⟩ := h0
    apply Or.inl
    apply isUnit_of_mul_eq_one_right (b := s0 * (↑(u⁻¹) : R))
    calc
      r0 * (s0 * (↑(u⁻¹) : R)) =
          (r0 * s0) * (↑(u⁻¹) : R) := by rw [mul_assoc]
      _ = (u : R) * (↑(u⁻¹) : R) := by rw [← hu]
      _ = 1 := Units.val_inv u
  · obtain ⟨u, hu⟩ := h1
    apply Or.inr
    apply isUnit_of_mul_eq_one_right (b := s 0 * (↑(u⁻¹) : R))
    calc
      r 0 * (s 0 * (↑(u⁻¹) : R)) =
          (r 0 * s 0) * (↑(u⁻¹) : R) := by rw [mul_assoc]
      _ = (u : R) * (↑(u⁻¹) : R) := by rw [← hu]
      _ = 1 := Units.val_inv u

/-- Every local ring satisfies Bass's condition `(S_1)`; compare Weibel,
*The K-book*, Exercise I.1.12(v). -/
theorem stableRangeCondition_one_of_isLocalRing [IsLocalRing R] :
    StableRangeCondition R 1 := by
  intro r0 r hr
  rcases isUnit_first_or_isUnit_second r0 r hr with h0 | h1
  · let a : Rˣ := h0.unit
    refine ⟨fun _ ↦ (↑(a⁻¹) : R) * (r 0 - 1), ?_⟩
    refine ⟨fun _ ↦ 1, ?_⟩
    rw [Fin.sum_univ_one]
    simp only [mul_one]
    have hInv : r0 * (↑(a⁻¹) : R) = 1 := by
      rw [← h0.unit_spec]
      exact Units.val_inv a
    rw [← mul_assoc, hInv, one_mul, sub_sub_cancel]
  · let a : Rˣ := h1.unit
    refine ⟨fun _ ↦ 0, ?_⟩
    refine ⟨fun _ ↦ (↑(a⁻¹) : R), ?_⟩
    rw [Fin.sum_univ_one]
    simp only [mul_zero, sub_zero]
    rw [← h1.unit_spec]
    exact Units.val_inv a

/-- In a nontrivial ring, Bass's condition `(S_0)` is impossible. -/
theorem not_stableRangeCondition_zero [Nontrivial R] :
    ¬ StableRangeCondition R 0 := by
  intro h
  let empty : Fin 0 → R := fun i ↦ Fin.elim0 i
  have hCons : IsRightUnimodularCons (1 : R) empty := by
    refine ⟨1, empty, ?_⟩
    simp [empty]
  obtain ⟨_, w, hw⟩ := h 1 empty hCons
  have h01 : (0 : R) = 1 := by
    simpa only [Finset.univ_eq_empty, Finset.sum_empty] using hw
  exact zero_ne_one h01

/-- Every local ring has least Bass stable range one; compare Weibel,
*The K-book*, Exercise I.1.12(v), with its source-local convention. -/
theorem stableRange_one_of_isLocalRing [IsLocalRing R] :
    IsStableRange R 1 := by
  refine ⟨stableRangeCondition_one_of_isLocalRing, ?_⟩
  intro n hn
  cases n with
  | zero => exact (not_stableRangeCondition_zero hn).elim
  | succ n => exact Nat.succ_le_succ (Nat.zero_le n)

end Bass

namespace IsLocalRing

universe u

variable {R : Type u} [Ring R] [IsLocalRing R]

/-- The Jacobson radical of a possibly noncommutative local ring consists exactly
of its nonunits; compare Weibel, *The K-book*, the local-ring discussion preceding
Lemma I.2.2 and the proof of that lemma.

Here locality is Mathlib's `IsLocalRing`, which includes nontriviality. Neither
commutativity nor a separate direct-finiteness hypothesis is required. -/
theorem mem_ringJacobson_iff (r : R) :
    r ∈ Ring.jacobson R ↔ ¬ IsUnit r := by
  constructor
  · intro hr
    exact coe_subset_nonunits (Ring.jacobson_lt_top R).ne hr
  · intro hr
    rw [← Ideal.jacobson_bot]
    apply Ideal.mem_jacobson_iff.mpr
    intro y
    -- A unit left multiple would give r a left inverse; use the opposite ring.
    have hneg : ¬ IsUnit ((-y) * r) := by
      intro h
      obtain ⟨u, hu⟩ := h
      have hleft : (↑(u⁻¹) : R) * (-y) * r = 1 := by
        rw [mul_assoc, ← hu]
        exact Units.inv_mul u
      have hright : MulOpposite.op r * MulOpposite.op ((↑(u⁻¹) : R) * (-y)) = 1 := by
        rw [← MulOpposite.op_mul, hleft, MulOpposite.op_one]
      exact hr (Bass.isUnit_of_mul_eq_one_right hright).unop
    -- Locality makes 1 + y * r a unit, supplying the Jacobson membership witness.
    have hsum : IsUnit (y * r + 1) := by
      simpa only [neg_mul, sub_neg_eq_add, add_comm] using
        isUnit_one_sub_self_of_mem_nonunits ((-y) * r) hneg
    obtain ⟨u, hu⟩ := hsum
    refine ⟨(↑(u⁻¹) : R), ?_⟩
    rw [Ideal.mem_bot, sub_eq_zero, mul_assoc, ← mul_add_one, ← hu]
    exact Units.inv_mul u

end IsLocalRing
