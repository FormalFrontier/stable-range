/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.CategoryTheory.Cancellation
public import StableRange.Regular
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Module.ULift
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod

/-!
# Free-summand cancellation from stable range one

This file proves that a module can be cancelled from a binary product whenever
its endomorphism ring satisfies Bass's right stable-range-one condition.
It specializes categorical biproduct cancellation, with no finiteness or
projectivity hypothesis on any module. Internal universe lifts put the
carriers in a common module category while preserving the original scalar
ring and the independent universes in the statement.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Exercise I.1.13(c) (unit-regular cancellation), and Exercise I.1.5(b)–(c)
  (stable-range cancellation context). The stable-range hypothesis here is
  more general than unit-regularity.
* `StableRange.CategoryTheory.Cancellation`, which generalizes this module
  theorem's original block proof using Mathlib's categorical Gaussian elimination.
* Mathlib, `LinearAlgebra.Pi`, `LinearAlgebra.Prod`, `Algebra.Module.ULift`,
  and `Algebra.Category.ModuleCat.Biproducts`, for linear equivalences,
  universe lifts and the module-category biproduct comparisons.
-/

set_option warningAsError true

@[expose] public section

namespace Bass

universe u v w x

variable {R : Type u} [Ring R]
variable {M : Type v} {A : Type w} {B : Type x}
variable [AddCommGroup M] [AddCommGroup A] [AddCommGroup B]
variable [Module R M] [Module R A] [Module R B]

/-- A module whose endomorphism ring satisfies `(S₁)` cancels from a binary
product. No finiteness or projectivity assumption is required. This strengthens
the cancellation setting of Weibel, *The K-book*, Exercise I.1.13(c). -/
theorem exists_linearEquiv_of_prod_of_end_stableRangeCondition_one
    (h : StableRangeCondition (Module.End R M) 1)
    (e : (M × A) ≃ₗ[R] (M × B)) :
    Nonempty (A ≃ₗ[R] B) := by
  -- Put the carriers in a common universe without changing the scalar ring.
  let m : ULift.{max v w x} M ≃ₗ[R] M := ULift.moduleEquiv
  let a : ULift.{max v w x} A ≃ₗ[R] A := ULift.moduleEquiv
  let b : ULift.{max v w x} B ≃ₗ[R] B := ULift.moduleEquiv
  let X : ModuleCat.{max v w x} R := ModuleCat.of R (ULift.{max v w x} M)
  let Y : ModuleCat.{max v w x} R := ModuleCat.of R (ULift.{max v w x} A)
  let Z : ModuleCat.{max v w x} R := ModuleCat.of R (ULift.{max v w x} B)
  have hX : StableRangeCondition (CategoryTheory.End X) 1 :=
    (h.map_equiv m.symm.conjRingEquiv).map_equiv (ModuleCat.endRingEquiv X).symm
  let e' : (ULift.{max v w x} M × ULift.{max v w x} A) ≃ₗ[R]
      (ULift.{max v w x} M × ULift.{max v w x} B) :=
    (m.prodCongr a).trans (e.trans (m.symm.prodCongr b.symm))
  obtain ⟨i⟩ := CategoryTheory.nonempty_iso_of_biprod_iso_of_end_stableRangeCondition_one
    X Y Z hX
    ((ModuleCat.biprodIsoProd X Y).trans
      (e'.toModuleIso.trans (ModuleCat.biprodIsoProd X Z).symm))
  exact ⟨a.symm.trans (i.toLinearEquiv.trans b)⟩

/-- If the endomorphism ring of `M` satisfies `(S₁)`, a finite free power of
`M` cannot absorb a nontrivial complementary module. -/
theorem subsingleton_of_pi_linearEquiv_pi_prod
    {P : Type x} [AddCommGroup P] [Module R P]
    (h : StableRangeCondition (Module.End R M) 1) (n : ℕ)
    (e : (Fin n → M) ≃ₗ[R] ((Fin n → M) × P)) :
    Subsingleton P := by
  induction n with
  | zero =>
      constructor
      intro x y
      let z : Fin 0 → M := 0
      have heq : e.symm (z, x) = e.symm (z, y) := Subsingleton.elim _ _
      have hpair : (z, x) = (z, y) := e.symm.injective heq
      exact congrArg Prod.snd hpair
  | succ n ih =>
      let split : (Fin (n + 1) → M) ≃ₗ[R] (M × (Fin n → M)) :=
        LinearEquiv.piCongrLeft R (fun _ ↦ M) (finSuccEquiv n) ≪≫ₗ
          .piOptionEquivProd _
      let reassoc : ((M × (Fin n → M)) × P) ≃ₗ[R]
          (M × ((Fin n → M) × P)) :=
        LinearEquiv.prodAssoc R M (Fin n → M) P
      let transformed : (M × (Fin n → M)) ≃ₗ[R]
          (M × ((Fin n → M) × P)) :=
        split.symm.trans (e.trans ((split.prodCongr (LinearEquiv.refl R P)).trans reassoc))
      obtain ⟨cancelled⟩ :=
        exists_linearEquiv_of_prod_of_end_stableRangeCondition_one h transformed
      exact ih cancelled

/-- A unit-regular ring satisfies the finite-free cancellation condition for
its regular right module. In Lean this right module is a left module over the
opposite ring. -/
theorem IsUnitRegular.subsingleton_of_fin_linearEquiv_fin_prod
    {P : Type x} [AddCommGroup P] [Module Rᵐᵒᵖ P]
    (h : IsUnitRegular R) (n : ℕ)
    (e : (Fin n → R) ≃ₗ[Rᵐᵒᵖ] ((Fin n → R) × P)) :
    Subsingleton P := by
  apply subsingleton_of_pi_linearEquiv_pi_prod _ n e
  exact h.stableRangeCondition_one.map_equiv (RingEquiv.moduleEndSelfOp R)

end Bass
