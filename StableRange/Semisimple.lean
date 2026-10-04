/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Product
public import StableRange.DivisionRing
public import StableRange.Quotient
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Semisimple rings and stable range

Semisimple rings satisfy the right Bass stable-range condition `(S₁)`, as do
rings whose quotient by the Jacobson radical is semisimple. Neither statement
assumes nilpotence of the radical.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Exercises I.1.5(c) and I.1.12(v) (Artinian stable range and radical quotients).
* Mathlib, `RingTheory.SimpleModule.WedderburnArtin` (semisimple rings as
  products of matrix rings over division rings); `general-linear-groups`,
  `QuasiregularIdeal` (Jacobson radical criterion).
-/

set_option warningAsError true

@[expose] public section

namespace Bass

universe u

/-- A semisimple ring satisfies the right Bass stable-range condition `(S₁)`.
The proof uses Mathlib's Wedderburn–Artin decomposition and the finite-matrix
stable-range theorem; compare Weibel, *The K-book*, Exercise I.1.5(c). -/
theorem stableRangeCondition_one_of_isSemisimpleRing
    {R : Type u} [Ring R] [IsSemisimpleRing R] :
    StableRangeCondition R 1 := by
  classical
  obtain ⟨m, D, d, hD, _, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
  let _ (i : Fin m) : DivisionRing (D i) := hD i
  have hMatrix (i : Fin m) :
      StableRangeCondition (Matrix (Fin (d i)) (Fin (d i)) (D i)) 1 :=
    (isUnitRegular_matrix (K := D i) (n := Fin (d i))).stableRangeCondition_one
  exact (stableRangeCondition_pi hMatrix).map_equiv e.symm

/-- If the quotient by the Jacobson radical is semisimple, the ring satisfies `(S₁)`. -/
theorem stableRangeCondition_one_of_isSemisimpleRing_quotient_jacobson
    {R : Type u} [Ring R]
    [IsSemisimpleRing (R ⧸ Ring.jacobson R)] :
    StableRangeCondition R 1 := by
  let J : TwoSidedIdeal R := (Ring.jacobson R).toTwoSided
  have hJ : J.asIdeal = Ring.jacobson R := by
    simpa only [J] using Ideal.asIdeal_toTwoSided (Ring.jacobson R)
  let e : (R ⧸ J.asIdeal) ≃+* (R ⧸ Ring.jacobson R) :=
    Ideal.quotientEquiv J.asIdeal (Ring.jacobson R) (RingEquiv.refl R)
      (by simpa using hJ.symm)
  have hquot : StableRangeCondition (R ⧸ J.asIdeal) 1 := by
    exact (stableRangeCondition_one_of_isSemisimpleRing
      (R := R ⧸ Ring.jacobson R)).map_equiv e.symm
  exact (stableRangeCondition_quotient_iff J
    TwoSidedIdeal.ringJacobson_isQuasiregular 1).mpr hquot

end Bass
