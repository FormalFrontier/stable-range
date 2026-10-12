/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import StableRange.Local

/-!
# Commutative agreement for the local maximal-left-ideal classification

Mathlib's `IsLocalRing.ringJacobson_eq_maximalIdeal` identifies the canonical
radical with the same maximal ideal used by its commutative classification.
These examples rewrite the three local-ring statements to the propositions of
Mathlib's `maximalIdeal.isMaximal`, `eq_maximalIdeal` and `isMaximal_iff`.
Over a field, `maximalIdeal_eq_bot` further identifies this ideal with zero.
The same radical equality turns the bound on proper left ideals into Mathlib's
`IsLocalRing.le_maximalIdeal` bound, with the same maximal-ideal object.

## References

* Mathlib, `RingTheory.LocalRing.MaximalIdeal.Basic` (the maximal-ideal
  classification, the radical equality and the field zero-ideal equality).
-/

universe u

section CommRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

example : (IsLocalRing.maximalIdeal R).IsMaximal := by
  simpa only [IsLocalRing.ringJacobson_eq_maximalIdeal R] using
    (IsLocalRing.isMaximal_ringJacobson R)

example {I : Ideal R} (hI : I.IsMaximal) : I = IsLocalRing.maximalIdeal R := by
  simpa only [IsLocalRing.ringJacobson_eq_maximalIdeal R] using
    (IsLocalRing.eq_ringJacobson hI)

example {I : Ideal R} : I.IsMaximal ↔ I = IsLocalRing.maximalIdeal R := by
  simpa only [IsLocalRing.ringJacobson_eq_maximalIdeal R] using
    (IsLocalRing.isMaximal_iff_eq_ringJacobson (R := R) (I := I))

example {I : Ideal R} (hI : I ≠ ⊤) : I ≤ IsLocalRing.maximalIdeal R := by
  simpa only [IsLocalRing.ringJacobson_eq_maximalIdeal R] using
    (IsLocalRing.le_ringJacobson hI)

end CommRing

section Field

variable (K : Type u) [Field K]

example : (⊥ : Ideal K).IsMaximal := by
  simpa only [IsLocalRing.ringJacobson_eq_maximalIdeal K,
    IsLocalRing.maximalIdeal_eq_bot] using
    (IsLocalRing.isMaximal_ringJacobson K)

example {I : Ideal K} (hI : I.IsMaximal) : I = ⊥ := by
  simpa only [IsLocalRing.ringJacobson_eq_maximalIdeal K,
    IsLocalRing.maximalIdeal_eq_bot] using
    (IsLocalRing.eq_ringJacobson hI)

example {I : Ideal K} : I.IsMaximal ↔ I = ⊥ := by
  simpa only [IsLocalRing.ringJacobson_eq_maximalIdeal K,
    IsLocalRing.maximalIdeal_eq_bot] using
    (IsLocalRing.isMaximal_iff_eq_ringJacobson (R := K) (I := I))

end Field
