/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Basic
public import GeneralLinearGroups.QuasiregularIdeal

/-!
# Stable range and quotients

This file proves descent of Bass stable-range conditions along surjective ring
homomorphisms and invariance under quotients by quasi-regular two-sided ideals.
-/

set_option warningAsError true

@[expose] public section

open Function
open scoped BigOperators

namespace Bass

universe u v

/-- If `(S_m)` holds in the domain, every right-unimodular row of length `m`
over the codomain of a surjective ring homomorphism has a right-unimodular
lift. -/
theorem exists_rightUnimodular_lift_of_surjective
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) (hf : Surjective f) {m : ℕ}
    (hm : StableRangeCondition R m) (q : Fin m → S)
    (hq : IsRightUnimodular q) :
    ∃ r : Fin m → R, (∀ i, f (r i) = q i) ∧ IsRightUnimodular r := by
  classical
  obtain ⟨w, hw⟩ := hq
  choose r hr using fun i ↦ hf (q i)
  choose b hb using fun i ↦ hf (w i)
  let e : R := 1 - ∑ i, r i * b i
  have he : f e = 0 := by
    simp only [e, map_sub, map_one, map_sum, map_mul, hr, hb]
    rw [hw, sub_self]
  have her : IsRightUnimodularCons e r := by
    refine ⟨1, b, ?_⟩
    simp [e]
  obtain ⟨t, ht⟩ := hm e r her
  refine ⟨fun i ↦ r i - e * t i, ?_, ht⟩
  intro i
  simp [hr i, he]

/-- Every Bass stable-range condition descends along a surjective ring
homomorphism. -/
theorem stableRangeCondition_of_surjective
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) (hf : Surjective f) {n : ℕ}
    (hn : StableRangeCondition R n) : StableRangeCondition S n := by
  intro q0 q hq
  let row : Fin (n + 1) → S := Fin.cases q0 q
  have hrow : IsRightUnimodular row := by
    apply (isRightUnimodular_finSucc_iff row).mpr
    simpa [row] using hq
  have hsucc : StableRangeCondition R (n + 1) :=
    stableRangeCondition_succ n hn
  obtain ⟨r, hr, hur⟩ :=
    exists_rightUnimodular_lift_of_surjective f hf hsucc row hrow
  obtain ⟨t, ht⟩ := (stableRangeCondition_iff_literal n).mp hn r hur
  refine ⟨fun i ↦ f (t i), ?_⟩
  have hmap := IsRightUnimodular.map f ht
  simpa only [map_sub, map_mul, hr, row, Fin.cases_zero, Fin.cases_succ] using hmap

/-- Every Bass stable-range condition descends to a two-sided quotient. -/
theorem stableRangeCondition_quotient
    {R : Type u} [Ring R] (I : TwoSidedIdeal R) {n : ℕ}
    (hn : StableRangeCondition R n) :
    StableRangeCondition (R ⧸ I.asIdeal) n :=
  stableRangeCondition_of_surjective (Ideal.Quotient.mk I.asIdeal)
    Ideal.Quotient.mk_surjective hn

/-- The least stable range of a two-sided quotient is at most that of the
original ring, conditional on supplied least indices. -/
theorem stableRange_quotient_le
    {R : Type u} [Ring R] (I : TwoSidedIdeal R) {sR sQ : ℕ}
    (hR : IsStableRange R sR)
    (hQ : IsStableRange (R ⧸ I.asIdeal) sQ) : sQ ≤ sR :=
  hQ.2 sR (stableRangeCondition_quotient I hR.1)

/-- A row whose image in a quotient by a quasi-regular two-sided ideal is
right-unimodular is already right-unimodular.

After lifting a quotient witness, its scalar product with the row differs from
`1` by an element of the ideal and is therefore a unit. Multiplying all
witnesses on the right by its inverse normalizes the product to `1`. -/
theorem isRightUnimodular_of_quotient
    {R : Type u} [Ring R] (I : TwoSidedIdeal R)
    (hI : I.IsQuasiregular) {n : ℕ} (r : Fin n → R)
    (hr : IsRightUnimodular
      (fun i ↦ Ideal.Quotient.mk I.asIdeal (r i))) :
    IsRightUnimodular r := by
  classical
  obtain ⟨q, hq⟩ := hr
  choose w hw using fun i ↦ Ideal.Quotient.mk_surjective (q i)
  let s : R := ∑ i, r i * w i
  have hsMap : Ideal.Quotient.mk I.asIdeal s = 1 := by
    simp only [s, map_sum, map_mul, hw]
    exact hq
  have hsMem : s - 1 ∈ I := by
    apply TwoSidedIdeal.mem_asIdeal.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp only [map_sub, map_one, hsMap, sub_self]
  have hsUnit : IsUnit s := by
    rw [I.isQuasiregular_iff_forall_isUnit_one_add] at hI
    simpa [add_comm] using hI (s - 1) hsMem
  let a : Rˣ := hsUnit.unit
  refine ⟨fun i ↦ w i * (↑(a⁻¹) : R), ?_⟩
  calc
    ∑ i, r i * (w i * (↑(a⁻¹) : R)) =
        s * (↑(a⁻¹) : R) := by
      simp only [s, mul_assoc, Finset.sum_mul]
    _ = 1 := by
      rw [← hsUnit.unit_spec]
      exact Units.val_inv a

/-- A quasi-regular quotient satisfies exactly the same Bass stable-range
conditions as the original ring. -/
theorem stableRangeCondition_quotient_iff
    {R : Type u} [Ring R] (I : TwoSidedIdeal R)
    (hI : I.IsQuasiregular) (n : ℕ) :
    StableRangeCondition R n ↔
      StableRangeCondition (R ⧸ I.asIdeal) n := by
  classical
  let f : R →+* R ⧸ I.asIdeal := Ideal.Quotient.mk I.asIdeal
  constructor
  · exact stableRangeCondition_quotient I
  · intro hQ r0 r hr
    have hq : IsRightUnimodularCons (f r0) (fun i ↦ f (r i)) :=
      IsRightUnimodularCons.map f hr
    obtain ⟨q, hq⟩ := hQ (f r0) (fun i ↦ f (r i)) hq
    choose t ht using fun i ↦ Ideal.Quotient.mk_surjective (q i)
    refine ⟨t, isRightUnimodular_of_quotient I hI _ ?_⟩
    simpa only [map_sub, map_mul, ht] using hq

/-- Quotienting by a quasi-regular two-sided ideal preserves supplied least
stable-range indices. -/
theorem stableRange_eq_quotient
    {R : Type u} [Ring R] (I : TwoSidedIdeal R)
    (hI : I.IsQuasiregular) {sR sQ : ℕ}
    (hR : IsStableRange R sR)
    (hQ : IsStableRange (R ⧸ I.asIdeal) sQ) : sR = sQ := by
  apply le_antisymm
  · exact hR.2 sQ ((stableRangeCondition_quotient_iff I hI sQ).mpr hQ.1)
  · exact hQ.2 sR ((stableRangeCondition_quotient_iff I hI sR).mp hR.1)

end Bass
