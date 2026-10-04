/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.FiniteFree
public import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Finite-free cancellation clients

The field presentation, the presentation with no stabilizing coordinates, the
independent-universe presentation and the zero-ring presentation are obtained
without using the cancellation construction. Its uses below exercise the
separately stated public conclusion.
-/

set_option warningAsError true

@[expose] public section

namespace StableRangeTests.FiniteFreeClient

/-- Three field coordinates presented as two coordinates and one free summand. -/
def fieldPresentation :
    ((Fin 2 → ℚ) × (Fin 1 → ℚ)) ≃ₗ[ℚ] (Fin 3 → ℚ) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 1) ℚ ℚ).symm.trans
    (LinearEquiv.piCongrLeft ℚ (fun _ : Fin 3 ↦ ℚ) finSumFinEquiv)

private theorem fieldStableRange : Bass.StableRangeCondition ℚ 1 :=
  Bass.stableRangeCondition_succ_of_krullDimLE (R := ℚ) (d := 0)

private noncomputable def fieldCancellation :
    (Fin 2 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  Module.finLinearEquivOfStableRangeCondition ℚ (Fin 2 → ℚ)
    fieldStableRange (by decide) fieldPresentation

private noncomputable def fieldDimensionCancellation :
    (Fin 2 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  Module.finLinearEquivOfKrullDimLE ℚ (Fin 2 → ℚ)
    (d := 0) (by decide) fieldPresentation

private theorem fieldFree : Module.Free ℚ (Fin 2 → ℚ) :=
  Module.Free.of_finProdEquiv_of_stableRangeCondition ℚ (Fin 2 → ℚ)
    fieldStableRange (by decide) fieldPresentation

private def emptyStabilizerPresentation :
    ((Fin 2 → ℚ) × (Fin 0 → ℚ)) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  LinearEquiv.prodUnique

private noncomputable def emptyStabilizerCancellation :
    (Fin 2 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  Module.finLinearEquivOfStableRangeCondition ℚ (Fin 2 → ℚ)
    fieldStableRange (by decide) emptyStabilizerPresentation

private def liftedPresentation :
    (ULift.{1} (Fin 2 → ℚ) × (Fin 1 → ℚ)) ≃ₗ[ℚ] (Fin 3 → ℚ) :=
  ((ULift.moduleEquiv (R := ℚ) (M := Fin 2 → ℚ)).prodCongr
    (LinearEquiv.refl ℚ (Fin 1 → ℚ))).trans fieldPresentation

private noncomputable def liftedCancellation :
    ULift.{1} (Fin 2 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  Module.finLinearEquivOfStableRangeCondition ℚ (ULift.{1} (Fin 2 → ℚ))
    fieldStableRange (by decide) liftedPresentation

private def zeroRingPresentation :
    ((Fin 0 → ZMod 1) × (Fin 0 → ZMod 1)) ≃ₗ[ZMod 1]
      (Fin 1 → ZMod 1) :=
  LinearEquiv.ofSubsingleton _ _

private theorem zeroRingStableRange : Bass.StableRangeCondition (ZMod 1) 0 := by
  intro _ _ _
  exact ⟨fun index ↦ Fin.elim0 index, ⟨fun index ↦ Fin.elim0 index,
    Subsingleton.elim _ _⟩⟩

private noncomputable def zeroRingCancellation :
    (Fin 0 → ZMod 1) ≃ₗ[ZMod 1] (Fin 1 → ZMod 1) :=
  Module.finLinearEquivOfStableRangeCondition (ZMod 1) (Fin 0 → ZMod 1)
    zeroRingStableRange (by decide) zeroRingPresentation

private def zeroRingEmptyPresentation :
    ((Fin 0 → ZMod 1) × (Fin 0 → ZMod 1)) ≃ₗ[ZMod 1]
      (Fin 0 → ZMod 1) :=
  LinearEquiv.prodUnique

private noncomputable def zeroRingEmptyCancellation :
    (Fin 0 → ZMod 1) ≃ₗ[ZMod 1] (Fin 0 → ZMod 1) :=
  Module.finLinearEquivOfStableRangeCondition (ZMod 1) (Fin 0 → ZMod 1)
    zeroRingStableRange (by decide) zeroRingEmptyPresentation

end StableRangeTests.FiniteFreeClient
