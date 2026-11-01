/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Module.LocalEnd
public import StableRange.Module.Radical
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Semisimple quotients from finite decompositions

A module that is linearly equivalent to a finite product of finitely generated projective
modules with local endomorphism rings has semisimple quotient by its Jacobson radical.
For the canonical left regular module, this gives a semisimple quotient ring.

The decomposition is an input; no condition on homomorphisms between distinct factors is
required. Both results include empty decompositions and the zero ambient module or ring.

## Main results

* `Module.isSemisimpleModule_quotient_jacobson_of_linearEquiv_pi`
* `Ring.isSemisimpleRing_quotient_jacobson_of_linearEquiv_pi`
-/

@[expose] public section

universe u v v' w

namespace Module

variable {R : Type u} [Ring R] {N : Type v} [AddCommGroup N] [Module R N]
  {ι : Type w} [Finite ι] {M : ι → Type v'}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, Projective R (M i)] [∀ i, Module.Finite R (M i)]
  [∀ i, IsLocalRing (End R (M i))]

/-- A finite decomposition into finitely generated projective modules with local
endomorphism rings makes the quotient by the module Jacobson radical semisimple. -/
theorem isSemisimpleModule_quotient_jacobson_of_linearEquiv_pi
    (e : N ≃ₗ[R] Π i, M i) : IsSemisimpleModule R (N ⧸ jacobson R N) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let qProd : (Π i, M i) →ₗ[R] Π i, M i ⧸ jacobson R (M i) :=
    LinearMap.piMap fun i => (jacobson R (M i)).mkQ
  let q : N →ₗ[R] Π i, M i ⧸ jacobson R (M i) := qProd.comp e.toLinearMap
  have hqProd : Function.Surjective qProd := by
    intro y
    refine ⟨fun i => Classical.choose ((jacobson R (M i)).mkQ_surjective (y i)), ?_⟩
    funext i
    exact Classical.choose_spec ((jacobson R (M i)).mkQ_surjective (y i))
  have hq : Function.Surjective q := hqProd.comp e.surjective
  have hkerProd : LinearMap.ker qProd =
      Submodule.pi Set.univ (fun i => jacobson R (M i)) := by
    ext x
    constructor
    · intro hx
      apply Submodule.mem_pi.mpr
      intro i _
      have hi : (jacobson R (M i)).mkQ (x i) = 0 :=
        congr_fun (LinearMap.mem_ker.mp hx) i
      have hmem : x i ∈ LinearMap.ker (jacobson R (M i)).mkQ :=
        LinearMap.mem_ker.mpr hi
      simpa only [Submodule.ker_mkQ] using hmem
    · intro hx
      apply LinearMap.mem_ker.mpr
      funext i
      have hmem : x i ∈ LinearMap.ker (jacobson R (M i)).mkQ := by
        rw [Submodule.ker_mkQ]
        exact Submodule.mem_pi.mp hx i (Set.mem_univ i)
      exact LinearMap.mem_ker.mp hmem
  have hker : LinearMap.ker q = jacobson R N := by
    dsimp only [q]
    rw [LinearMap.ker_comp, hkerProd, ← jacobson_pi R M]
    exact comap_jacobson_of_bijective (f := e.toLinearMap) e.bijective
  let eQ : (N ⧸ jacobson R N) ≃ₗ[R] Π i, M i ⧸ jacobson R (M i) :=
    (Submodule.quotEquivOfEq (jacobson R N) (LinearMap.ker q) hker.symm).trans
      (q.quotKerEquivOfSurjective hq)
  let : ∀ i, IsSimpleModule R (M i ⧸ jacobson R (M i)) := fun i =>
    isSimpleModule_quotient_jacobson_of_isLocalRing_end (R := R) (P := M i)
  let : IsSemisimpleModule R (Π₀ i, M i ⧸ jacobson R (M i)) := inferInstance
  let : IsSemisimpleModule R (Π i, M i ⧸ jacobson R (M i)) :=
    IsSemisimpleModule.congr
      (DFinsupp.linearEquivFunOnFintype :
        (Π₀ i, M i ⧸ jacobson R (M i)) ≃ₗ[R] Π i, M i ⧸ jacobson R (M i)).symm
  exact IsSemisimpleModule.congr eQ

end Module

namespace Ring

variable {R : Type u} [Ring R] {ι : Type w} [Finite ι] {M : ι → Type v'}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, Module.Projective R (M i)] [∀ i, Module.Finite R (M i)]
  [∀ i, IsLocalRing (Module.End R (M i))]

/-- A finite decomposition of the canonical left regular module into finitely generated
projective modules with local endomorphism rings gives a semisimple Jacobson quotient
ring. -/
theorem isSemisimpleRing_quotient_jacobson_of_linearEquiv_pi
    (e : R ≃ₗ[R] Π i, M i) : IsSemisimpleRing (R ⧸ jacobson R) := by
  let : IsSemisimpleModule R (R ⧸ jacobson R) :=
    Module.isSemisimpleModule_quotient_jacobson_of_linearEquiv_pi e
  let q : R →+* R ⧸ jacobson R := Ideal.Quotient.mk (jacobson R)
  let : RingHomSurjective q :=
    ⟨Ideal.Quotient.mk_surjective (I := jacobson R)⟩
  -- The quotient action of R and left multiplication by its image agree.
  have hsmul (r : R) (s : R ⧸ jacobson R) : q r * s = r • s := by
    rfl
  let f : (R ⧸ jacobson R) →ₛₗ[q] R ⧸ jacobson R :=
    ⟨AddHom.id _, fun r s => (hsmul r s).symm⟩
  have hf : Function.Bijective f := ⟨Function.injective_id, Function.surjective_id⟩
  exact (LinearMap.isSemisimpleModule_iff_of_bijective f hf).mp inferInstance

end Ring
