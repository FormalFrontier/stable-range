/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Basic
public import Mathlib.RingTheory.LocalProperties.Semilocal

/-!
# Bass stable range over commutative semilocal rings

The finite maximal spectrum is expressed using Mathlib's `Finite (MaximalSpectrum R)`
convention. Right-unimodular pairs have a distinguished first entry `a`, and the
remaining entry is shortened in the form `b - a * t`. The zero ring is included.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter I, §1 (Bass stable range and its maximal-spectrum dimension bound).
  The finite-spectrum proof here uses simultaneous maximal-ideal avoidance.
* Mathlib, `RingTheory.LocalProperties.Semilocal` (the finite maximal spectrum)
  and the Chinese remainder and maximal-ideal unit criteria used here.
-/

set_option warningAsError true

@[expose] public section

open Function

namespace Bass

/-- A commutative ring with finitely many maximal ideals satisfies Bass's `(S₁)`.
The right-unimodular reduction replaces `b` by `b - a * t`, including when the
maximal spectrum is empty. The maximal-ideal avoidance proof uses Mathlib's
finite Chinese remainder interface; compare the stable-range dimension
discussion in Weibel, *The K-book*, Chapter I, §1. -/
theorem stableRangeCondition_one_of_finite_maximalSpectrum
    {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)] :
    StableRangeCondition R 1 := by
  classical
  intro a row hrow
  obtain ⟨s₀, s, hs⟩ := hrow
  let b := row 0
  have hpair : a * s₀ + b * s 0 = 1 := by
    simpa only [Fin.sum_univ_one] using hs
  let coefficient : MaximalSpectrum R → R := fun m => if b ∈ m.asIdeal then 1 else 0
  have havoid : ∀ m : MaximalSpectrum R, b - a * coefficient m ∉ m.asIdeal := by
    intro m
    by_cases hb : b ∈ m.asIdeal
    · have ha : a ∉ m.asIdeal := by
        intro ha
        have hone : (1 : R) ∈ m.asIdeal := by
          rw [← hpair]
          exact m.asIdeal.add_mem
            (m.asIdeal.mul_mem_right s₀ ha) (m.asIdeal.mul_mem_right (s 0) hb)
        exact m.isMaximal.ne_top (m.asIdeal.eq_top_iff_one.mpr hone)
      intro hba
      have hba' : b - a ∈ m.asIdeal := by simpa [coefficient, hb] using hba
      apply ha
      convert m.asIdeal.sub_mem hb hba' using 1; ring
    · simp [coefficient, hb]
  have hcoprime : Pairwise (IsCoprime on fun m : MaximalSpectrum R => m.asIdeal) := by
    intro m n hne
    exact MaximalSpectrum.isCoprime_of_ne hne
  obtain ⟨t, ht⟩ := Ideal.exists_forall_sub_mem_ideal hcoprime coefficient
  have hnot : ∀ m : MaximalSpectrum R, b - a * t ∉ m.asIdeal := by
    intro m hm
    apply havoid m
    have hdiff : a * (t - coefficient m) ∈ m.asIdeal :=
      m.asIdeal.mul_mem_left a (ht m)
    have heq : (b - a * t) + a * (t - coefficient m) = b - a * coefficient m := by
      ring
    rw [← heq]
    exact m.asIdeal.add_mem hm hdiff
  have hunit : IsUnit (b - a * t) := by
    apply Ideal.span_singleton_eq_top.mp
    by_contra hproper
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hproper
    exact hnot ⟨M, hM⟩ (hle (Ideal.mem_span_singleton_self _))
  obtain ⟨w, hw⟩ := hunit.exists_right_inv
  refine ⟨fun _ => t, fun _ => w, ?_⟩
  simpa only [IsRightUnimodular, Fin.sum_univ_one] using hw

end Bass
