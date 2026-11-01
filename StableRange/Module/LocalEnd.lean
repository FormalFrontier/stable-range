/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Projective modules with local endomorphism semirings

A projective module with local endomorphism semiring cannot be the sum of two proper
submodules. If it is finitely generated, it has a unique maximal submodule. Over a ring,
its quotient by the Jacobson radical is therefore simple.

## Main results

* `Submodule.eq_top_or_eq_top_of_sup_eq_top_of_isLocalRing_end`: one of two submodules
  whose sum is the whole projective module is the whole module.
* `Module.existsUnique_isCoatom_of_isLocalRing_end`: a finitely generated projective
  module with local endomorphism semiring has a unique maximal submodule.
* `Module.isSimpleModule_quotient_jacobson_of_isLocalRing_end`: the quotient of such a
  module by its Jacobson radical is simple.

## References

* Formal Frontier Agents, *Local projective summands and the radical quotient*.
-/

@[expose] public section

universe u v

namespace Submodule

variable {R : Type u} {P : Type v} [Semiring R] [AddCommMonoid P] [Module R P]
  [Module.Projective R P] [IsLocalRing (Module.End R P)]

/-- A projective module with local endomorphism semiring is not the sum of two proper
submodules. Finite generation is not required. -/
theorem eq_top_or_eq_top_of_sup_eq_top_of_isLocalRing_end
    (N L : Submodule R P) (h : N ⊔ L = ⊤) : N = ⊤ ∨ L = ⊤ := by
  let q : N × L →ₗ[R] P := N.subtype.coprod L.subtype
  have hq : Function.Surjective q := by
    intro x
    have hx : x ∈ N ⊔ L := by simp only [h, Submodule.mem_top]
    obtain ⟨y, z, hyz⟩ := Submodule.mem_sup'.mp hx
    exact ⟨(y, z), hyz⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q (LinearMap.id : P →ₗ[R] P) hq
  let α : Module.End R P := N.subtype.comp ((LinearMap.fst R N L).comp s)
  let β : Module.End R P := L.subtype.comp ((LinearMap.snd R N L).comp s)
  have hαβ : α + β = 1 := by
    ext x
    change q (s x) = x
    exact LinearMap.congr_fun hs x
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hαβ with hα | hβ
  · left
    apply top_unique
    intro x _
    rw [← Module.End.isUnit_apply_inv_apply_of_isUnit hα x]
    exact (s (hα.unit.inv x)).1.property
  · right
    apply top_unique
    intro x _
    rw [← Module.End.isUnit_apply_inv_apply_of_isUnit hβ x]
    exact (s (hβ.unit.inv x)).2.property

end Submodule

namespace Module

private theorem nontrivial_of_isLocalRing_end
    (R : Type u) (P : Type v) [Semiring R] [AddCommMonoid P] [Module R P]
    [IsLocalRing (End R P)] : Nontrivial P := by
  classical
  by_cases h : ∃ x : P, x ≠ 0
  · obtain ⟨x, hx⟩ := h
    exact ⟨⟨x, 0, hx⟩⟩
  · have hzero : ∀ x : P, x = 0 := by
      intro x
      by_contra hx
      exact h ⟨x, hx⟩
    exfalso
    apply (zero_ne_one : (0 : End R P) ≠ 1)
    ext x
    exact (hzero x).symm

section Semiring

variable {R : Type u} {P : Type v} [Semiring R] [AddCommMonoid P] [Module R P]
  [Projective R P] [Module.Finite R P] [IsLocalRing (End R P)]

/-- A finitely generated projective module with local endomorphism semiring has a
unique maximal submodule. Nontriviality follows from locality of its endomorphisms. -/
theorem existsUnique_isCoatom_of_isLocalRing_end : ∃! N : Submodule R P, IsCoatom N := by
  classical
  let : Nontrivial P := nontrivial_of_isLocalRing_end (R := R) (P := P)
  obtain ⟨N, hN, -⟩ :=
    (eq_top_or_exists_le_coatom (⊥ : Submodule R P)).resolve_left bot_ne_top
  refine ⟨N, hN, ?_⟩
  intro L hL
  by_contra hLN
  have hsup : L ⊔ N = ⊤ := hL.sup_eq_top_of_ne hN hLN
  rcases Submodule.eq_top_or_eq_top_of_sup_eq_top_of_isLocalRing_end L N hsup with
    hLtop | hNtop
  · exact hL.ne_top hLtop
  · exact hN.ne_top hNtop

end Semiring

section Ring

variable {R : Type u} {P : Type v} [Ring R] [AddCommGroup P] [Module R P]
  [Projective R P] [Module.Finite R P] [IsLocalRing (End R P)]

/-- The quotient of a finitely generated projective module with local endomorphism
ring by its Jacobson radical is simple. -/
theorem isSimpleModule_quotient_jacobson_of_isLocalRing_end :
    IsSimpleModule R (P ⧸ jacobson R P) := by
  obtain ⟨N, hN, hunique⟩ := existsUnique_isCoatom_of_isLocalRing_end (R := R) (P := P)
  have hrad : jacobson R P = N := by
    change sInf {L : Submodule R P | IsCoatom L} = N
    apply le_antisymm
    · exact sInf_le hN
    · refine le_sInf ?_
      intro L hL
      exact le_of_eq (hunique L hL).symm
  apply isSimpleModule_iff_isCoatom.mpr
  rw [hrad]
  exact hN

end Ring

end Module
