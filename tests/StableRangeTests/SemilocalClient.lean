/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.Algebra.Group.Int.Units

/-!
# Semilocal stable-range clients

These examples exercise the finite-maximal-spectrum hypothesis, right-handed
shortening and the existing stable quotient determinant API.

## References

* Mathlib, `Data.ZMod.Basic`, `Algebra.Field.ZMod` and
  `RingTheory.Artinian.Module` (finite maximal-spectrum fixtures).
-/

set_option warningAsError true

@[expose] public section

namespace StableRangeTests.SemilocalClient

open Matrix.GeneralLinearGroup

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private abbrev Coefficients := ZMod 2 × ZMod 2

private def firstEntry : Coefficients := (1, 0)
private def secondEntry : Coefficients := (0, 1)

private theorem entries_nonunit : ¬ IsUnit firstEntry ∧ ¬ IsUnit secondEntry := by
  constructor <;> simp [firstEntry, secondEntry]

private theorem ring_nonlocal : ¬ IsLocalRing Coefficients := by
  intro hlocal
  have hnonunit : ¬ IsUnit (firstEntry + secondEntry) :=
    @IsLocalRing.nonunits_add Coefficients _ hlocal _ _ entries_nonunit.1 entries_nonunit.2
  apply hnonunit
  have hsum : firstEntry + secondEntry = 1 := by decide
  simpa only [hsum] using (isUnit_one : IsUnit (1 : Coefficients))

/-- The nonlocal ring `ZMod 2 × ZMod 2` has finite maximal spectrum. -/
theorem finite_maximalSpectrum_product :
    Finite (MaximalSpectrum (ZMod 2 × ZMod 2)) := by
  infer_instance

private theorem right_unimodular_pair :
    Bass.IsRightUnimodularCons firstEntry (fun _ : Fin 1 ↦ secondEntry) := by
  refine ⟨1, fun _ ↦ 1, ?_⟩
  simp [firstEntry, secondEntry, Prod.ext_iff]

/-- A right-unimodular pair over a nonlocal product of fields has neither
entry invertible but admits a shortening `b - a * t` to a unit. -/
private theorem nonlocal_pair_shortening :
    ¬ IsUnit firstEntry ∧ ¬ IsUnit secondEntry ∧ ¬ IsLocalRing Coefficients ∧
      ∃ t w : Coefficients, (secondEntry - firstEntry * t) * w = 1 := by
  let finite : Finite (MaximalSpectrum Coefficients) := finite_maximalSpectrum_product
  obtain ⟨t, witness, hwitness⟩ :=
    Bass.stableRangeCondition_one_of_finite_maximalSpectrum
      firstEntry (fun _ : Fin 1 ↦ secondEntry) right_unimodular_pair
  refine ⟨entries_nonunit.1, entries_nonunit.2, ring_nonlocal, t 0, witness 0, ?_⟩
  simpa only [Bass.IsRightUnimodular, Fin.sum_univ_one] using hwitness

private theorem explicit_coefficient :
    secondEntry - firstEntry * firstEntry = 1 := by
  decide

private theorem zero_ring_shortening (a b : ZMod 1) :
    ∃ t w : ZMod 1, (b - a * t) * w = 1 := by
  let artinian : IsArtinianRing (ZMod 1) := Ring.isArtinian_of_zero_eq_one (Subsingleton.elim _ _)
  let finite : Finite (MaximalSpectrum (ZMod 1)) := inferInstance
  have hpair : Bass.IsRightUnimodularCons a (fun _ : Fin 1 ↦ b) := by
    refine ⟨0, fun _ ↦ 0, ?_⟩
    exact Subsingleton.elim _ _
  obtain ⟨t, witness, hwitness⟩ :=
    Bass.stableRangeCondition_one_of_finite_maximalSpectrum a (fun _ : Fin 1 ↦ b) hpair
  exact ⟨t 0, witness 0,
    by simpa only [Bass.IsRightUnimodular, Fin.sum_univ_one] using hwitness⟩

private theorem local_ring_shortening {R : Type*} [CommRing R] [IsLocalRing R]
    (a b : R) (hpair : Bass.IsRightUnimodularCons a (fun _ : Fin 1 ↦ b)) :
    ∃ t w : R, (b - a * t) * w = 1 := by
  let finite : Finite (MaximalSpectrum R) := inferInstance
  obtain ⟨t, witness, hwitness⟩ :=
    Bass.stableRangeCondition_one_of_finite_maximalSpectrum a (fun _ : Fin 1 ↦ b) hpair
  exact ⟨t 0, witness 0,
    by simpa only [Bass.IsRightUnimodular, Fin.sum_univ_one] using hwitness⟩

private theorem integer_pair_right_unimodular :
    Bass.IsRightUnimodularCons (5 : ℤ) (fun _ : Fin 1 ↦ (2 : ℤ)) := by
  refine ⟨1, fun _ ↦ -2, ?_⟩
  norm_num [Fin.sum_univ_one]

private theorem integer_pair_no_shortening :
    ¬ ∃ t w : ℤ, (2 - 5 * t) * w = 1 := by
  rintro ⟨t, w, hw⟩
  have hunit : IsUnit (2 - 5 * t : ℤ) := isUnit_iff_exists_inv.mpr ⟨w, hw⟩
  rcases Int.isUnit_iff.mp hunit with h | h <;> omega

private theorem integer_fails_stable_range_one :
    ¬ Bass.StableRangeCondition ℤ 1 := by
  intro stable
  obtain ⟨t, witness, hwitness⟩ :=
    stable 5 (fun _ : Fin 1 ↦ 2) integer_pair_right_unimodular
  apply integer_pair_no_shortening
  exact ⟨t 0, witness 0,
    by simpa only [Bass.IsRightUnimodular, Fin.sum_univ_one] using hwitness⟩

example : Bass.StableRangeCondition (Matrix (Fin 0) (Fin 0) ℤ) 1 ∧
    ¬ Bass.StableRangeCondition ℤ 1 := by
  refine ⟨?_, integer_fails_stable_range_one⟩
  intro _ _ _
  refine ⟨fun _ ↦ 0, fun _ ↦ 0, ?_⟩
  exact Subsingleton.elim _ _

example : ¬ Bass.StableRangeCondition (Matrix (Fin 1) (Fin 1) ℤ) 1 := by
  intro matrixCondition
  exact integer_fails_stable_range_one
    (matrixCondition.map_equiv Matrix.uniqueRingEquiv)

private theorem semilocal_stable_quotient_determinant
    (first second : StableGL Coefficients ⧸ stableElementarySubgroup Coefficients)
    (hdet : StableGL.quotientDet Coefficients first =
      StableGL.quotientDet Coefficients second) : first = second := by
  let finite : Finite (MaximalSpectrum Coefficients) := finite_maximalSpectrum_product
  exact (StableGL.quotientDet_eq_iff_of_stableRangeCondition_one
    Bass.stableRangeCondition_one_of_finite_maximalSpectrum first second).mp hdet

end StableRangeTests.SemilocalClient
