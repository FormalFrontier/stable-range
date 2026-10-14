/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import StableRange.Module.SplitSurjective
import Mathlib.Tactic.NormNum

/-!
# Natural-scalar split-kernel decompositions

The horizontal and diagonal sections of the first projection `ℤ × ℤ → ℤ`
give different kernel coordinates of `(3, 5)` while preserving its image and
reconstructing the vector. The identity map gives a zero-kernel boundary case.
These examples use Mathlib's canonical `ℕ`-modules and product linear maps.
-/

namespace StableRangeTests.ModuleSplit

private abbrev projection : (ℤ × ℤ) →ₗ[ℕ] ℤ := LinearMap.fst ℕ ℤ ℤ
private abbrev horizontalSection : ℤ →ₗ[ℕ] ℤ × ℤ := LinearMap.inl ℕ ℤ ℤ
private abbrev diagonalSection : ℤ →ₗ[ℕ] ℤ × ℤ :=
  (LinearMap.id : ℤ →ₗ[ℕ] ℤ).prod LinearMap.id

private noncomputable abbrev horizontalSplit : (projection.ker × ℤ) ≃ₗ[ℕ] (ℤ × ℤ) :=
  LinearMap.kerProdEquivOfRightInverse projection horizontalSection
    (LinearMap.fst_comp_inl ℕ ℤ ℤ)
private noncomputable abbrev diagonalSplit : (projection.ker × ℤ) ≃ₗ[ℕ] (ℤ × ℤ) :=
  LinearMap.kerProdEquivOfRightInverse projection diagonalSection
    (LinearMap.fst_prod (LinearMap.id : ℤ →ₗ[ℕ] ℤ) LinearMap.id)

example : ((horizontalSplit.symm (3, 5)).1 : ℤ × ℤ) = (0, 5) ∧
    (horizontalSplit.symm (3, 5)).2 = 3 := by
  constructor
  · rw [LinearMap.kerProdEquivOfRightInverse_symm_fst]
    rfl
  · rw [LinearMap.kerProdEquivOfRightInverse_symm_snd]
    rfl

example : ((diagonalSplit.symm (3, 5)).1 : ℤ × ℤ) = (0, 2) ∧
    (diagonalSplit.symm (3, 5)).2 = 3 := by
  constructor
  · rw [LinearMap.kerProdEquivOfRightInverse_symm_fst]
    rfl
  · rw [LinearMap.kerProdEquivOfRightInverse_symm_snd]
    rfl

example : horizontalSplit
    (⟨(0, 5), by simp [projection, LinearMap.mem_ker]⟩, 3) = (3, 5) := by
  rw [LinearMap.kerProdEquivOfRightInverse_apply]
  rfl

example : diagonalSplit
    (⟨(0, 2), by simp [projection, LinearMap.mem_ker]⟩, 3) = (3, 5) := by
  rw [LinearMap.kerProdEquivOfRightInverse_apply]
  rfl

example : horizontalSplit (horizontalSplit.symm (3, 5)) = (3, 5) ∧
    diagonalSplit (diagonalSplit.symm (3, 5)) = (3, 5) :=
  ⟨horizontalSplit.apply_symm_apply _, diagonalSplit.apply_symm_apply _⟩

example : (horizontalSplit.symm (1, 1)).1 ≠ 0 ∧
    (horizontalSplit.symm (1, 1)).2 ≠ 0 := by
  constructor
  · intro h
    have hv := congrArg (fun k : projection.ker ↦ k.val) h
    rw [LinearMap.kerProdEquivOfRightInverse_symm_fst] at hv
    exact one_ne_zero (congrArg Prod.snd hv)
  · rw [LinearMap.kerProdEquivOfRightInverse_symm_snd]
    exact one_ne_zero

example : (horizontalSplit.symm (3, 5)).1 ≠ (diagonalSplit.symm (3, 5)).1 := by
  intro h
  have hv := congrArg (fun k : projection.ker ↦ k.val) h
  rw [LinearMap.kerProdEquivOfRightInverse_symm_fst,
    LinearMap.kerProdEquivOfRightInverse_symm_fst] at hv
  have hn : (5 : ℤ) = 2 := congrArg Prod.snd hv
  norm_num at hn

example (x : ℤ) : (LinearMap.id : ℤ →ₗ[ℕ] ℤ).ker = ⊥ ∧
    (LinearMap.kerProdEquivOfRightInverse (LinearMap.id : ℤ →ₗ[ℕ] ℤ)
      LinearMap.id (LinearMap.id_comp _)).symm x = (0, x) := by
  refine ⟨LinearMap.ker_id, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    simp only [LinearMap.kerProdEquivOfRightInverse_symm_fst, LinearMap.id_apply,
      sub_self, ZeroMemClass.coe_zero]
  · exact LinearMap.kerProdEquivOfRightInverse_symm_snd _ _ _ _

end StableRangeTests.ModuleSplit
