/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Jacobson.Radical

/-!
# Jacobson radicals of finite products of modules

For a finite family of modules, `Module.jacobson_pi` identifies the Jacobson radical of their
product with the product of their Jacobson radicals. It complements `Module.jacobson_pi_le`,
which holds for arbitrary families.
-/

@[expose] public section

open scoped BigOperators

universe u v w

namespace Module

variable (R : Type u) [Ring R] {ι : Type w} [Finite ι]
  (M : ι → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The Jacobson radical of a finite product of modules is the product of their
Jacobson radicals. -/
theorem jacobson_pi :
    jacobson R (Π i, M i) = Submodule.pi Set.univ (fun i => jacobson R (M i)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  refine le_antisymm (jacobson_pi_le R M) ?_
  intro x hx
  have hsingle (i : ι) : Pi.single i (x i) ∈ jacobson R (Π i, M i) := by
    exact map_jacobson_le (LinearMap.single R M i) <|
      Submodule.mem_map.mpr ⟨x i, Submodule.mem_pi.mp hx i (Set.mem_univ i), rfl⟩
  have hsum : (∑ i, Pi.single i (x i)) ∈ jacobson R (Π i, M i) :=
    (jacobson R (Π i, M i)).sum_mem fun i _ => hsingle i
  simpa only [LinearMap.sum_single_apply] using hsum

end Module
