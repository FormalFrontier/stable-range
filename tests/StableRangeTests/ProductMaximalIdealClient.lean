/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import StableRange
import StableRangeTests.DivisionSemiringClient
public import Mathlib.Algebra.Quaternion
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.LocalRing.NonLocalRing

/-!
# Maximal left ideals of nonlocal products

For a product of division rings, the two canonical projection kernels are
proper, distinct maximal left ideals. Their maximality comes from surjectivity
of the projections and Mathlib's division-ring kernel theorem, not from a
local-ring classification or a quotient construction. The complementary
coordinate elements are nonunits summing to one, directly contradicting
locality; the nonlocality conclusion uses Mathlib's product theorem.
Specializing to real quaternions gives a noncommutative boundary.
All statements use the canonical product ring structure. The generic factors
may lie in different universes.

## References

* Mathlib, `RingTheory.Ideal.Maps` and `RingTheory.Ideal.Maximal`, for maximal
  left kernels of surjections to division rings; `Algebra.Ring.Prod`, for
  the canonical projections; and `RingTheory.LocalRing.NonLocalRing`, for
  nonlocality of products of nontrivial semirings.
* `StableRangeTests.DivisionSemiringClient`, for the independent quaternion
  noncommutativity witness reused here.
* `ProjectiveModulesTests.LocalRingClient`, for the separation of private
  nonlocal scalar-ring controls from module conclusions; no module theorem
  is used in these ring controls.
-/

set_option warningAsError true

namespace StableRangeTests.ProductMaximalIdealClient

open scoped Quaternion

universe u v

private theorem product_projection_kernels (D : Type u) (E : Type v)
    [DivisionRing D] [DivisionRing E] :
    (RingHom.ker (RingHom.fst D E)).IsMaximal ∧
      (RingHom.ker (RingHom.snd D E)).IsMaximal ∧
      RingHom.ker (RingHom.fst D E) ≠ ⊤ ∧
      RingHom.ker (RingHom.snd D E) ≠ ⊤ ∧
      RingHom.ker (RingHom.fst D E) ≠ RingHom.ker (RingHom.snd D E) := by
  have hfst := RingHom.ker_isMaximal_of_surjective (RingHom.fst D E)
    Prod.fst_surjective
  have hsnd := RingHom.ker_isMaximal_of_surjective (RingHom.snd D E)
    Prod.snd_surjective
  refine ⟨hfst, hsnd, hfst.ne_top, hsnd.ne_top, ?_⟩
  intro h
  have hmem : ((0, 1) : D × E) ∈ RingHom.ker (RingHom.fst D E) := by
    rw [RingHom.mem_ker]
    rfl
  have hmem' : ((0, 1) : D × E) ∈ RingHom.ker (RingHom.snd D E) := h ▸ hmem
  have h10 : (1 : E) = 0 := by
    simpa only [RingHom.mem_ker, RingHom.coe_snd] using hmem'
  exact one_ne_zero h10

-- This unit obstruction needs neither division nor commutativity.
private theorem product_nonunit_summands (R : Type u) (S : Type v)
    [Semiring R] [Semiring S] [Nontrivial R] [Nontrivial S] :
    ¬ IsUnit ((1, 0) : R × S) ∧
      ¬ IsUnit ((0, 1) : R × S) ∧
      ((1, 0) : R × S) + ((0, 1) : R × S) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact not_isUnit_zero (M₀ := S)
      (by simpa using h.map (RingHom.snd R S))
  · intro h
    exact not_isUnit_zero (M₀ := R)
      (by simpa using h.map (RingHom.fst R S))
  · exact Prod.ext (add_zero (1 : R)) (zero_add (1 : S))

private theorem quaternion_product_noncommutative :
    ∃ x y : ℍ[ℝ] × ℍ[ℝ], x * y ≠ y * x := by
  obtain ⟨i, j, hij⟩ :=
    StableRangeTests.DivisionSemiringClient.quaternion_noncommutative
  refine ⟨(i, 0), (j, 0), ?_⟩
  intro h
  exact hij (congrArg Prod.fst h)

/-- The canonical product of two real quaternion division rings has two proper,
distinct maximal left ideals, namely its projection kernels. This test-only
counterexample witnesses why maximal-left-ideal uniqueness needs locality. -/
public theorem quaternion_product_maximal_ideals :
    (RingHom.ker (RingHom.fst ℍ[ℝ] ℍ[ℝ])).IsMaximal ∧
    (RingHom.ker (RingHom.snd ℍ[ℝ] ℍ[ℝ])).IsMaximal ∧
    RingHom.ker (RingHom.fst ℍ[ℝ] ℍ[ℝ]) ≠ ⊤ ∧
    RingHom.ker (RingHom.snd ℍ[ℝ] ℍ[ℝ]) ≠ ⊤ ∧
    RingHom.ker (RingHom.fst ℍ[ℝ] ℍ[ℝ]) ≠
      RingHom.ker (RingHom.snd ℍ[ℝ] ℍ[ℝ]) :=
  product_projection_kernels ℍ[ℝ] ℍ[ℝ]

example : ¬ IsUnit ((1, 0) : ℍ[ℝ] × ℍ[ℝ]) ∧
    ¬ IsUnit ((0, 1) : ℍ[ℝ] × ℍ[ℝ]) ∧
    ((1, 0) : ℍ[ℝ] × ℍ[ℝ]) + ((0, 1) : ℍ[ℝ] × ℍ[ℝ]) = 1 :=
  product_nonunit_summands ℍ[ℝ] ℍ[ℝ]

example : ¬ IsLocalRing (ℍ[ℝ] × ℍ[ℝ]) ∧
    ∃ x y : ℍ[ℝ] × ℍ[ℝ], x * y ≠ y * x :=
  ⟨IsLocalRing.not_isLocalRing_of_prod_of_nontrivial ℍ[ℝ] ℍ[ℝ],
    quaternion_product_noncommutative⟩

end StableRangeTests.ProductMaximalIdealClient
