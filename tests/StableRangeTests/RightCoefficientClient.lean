/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.RowKernel
public import StableRangeTests.RightCoefficientFixtures
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Right-coefficient section and kernel clients

The integer row tests the witness-dependent section, its split kernel and the
commutative kernel transport. Independent row arithmetic and boundary cases
live in `RightCoefficientFixtures`.
-/

set_option warningAsError true

@[expose] public section

namespace StableRangeTests.RightCoefficientClient

open StableRangeTests.RightCoefficientFixtures

private theorem integerSection_values (y : ℤ) :
    LinearMap.rightCoefficientSection ℤ integerWitness y = ![-y, y] := by
  funext i
  fin_cases i <;> simp [integerWitness, LinearMap.rightCoefficientSection_apply]

/-- The integer row applied to its explicit right-linear section returns the scalar. -/
theorem integerSection_originalRow (y : ℤ) :
    dotProductBilin ℤ ℤᵐᵒᵖ integerRow
      (LinearMap.rightCoefficientSection ℤ integerWitness y) = y := by
  have hsection : LinearMap.rightCoefficientSection ℤ integerWitness y =
      (fun i ↦ integerWitness i * y) := by
    funext i
    exact LinearMap.rightCoefficientSection_apply ℤ integerWitness y i
  rw [hsection]
  exact integerRow_on_witness y

/-- The explicit integer kernel element has nonzero underlying vector. -/
private def integerRightKernel :
    LinearMap.ker (dotProductBilin ℤ ℤᵐᵒᵖ integerRow) :=
  ⟨integerKernelVector, integerKernelVector_mem_ker⟩

private noncomputable def integerSplit :
    (LinearMap.ker (dotProductBilin ℤ ℤᵐᵒᵖ integerRow) × ℤ) ≃ₗ[ℤᵐᵒᵖ]
      (Fin 2 → ℤ) :=
  LinearEquiv.rightCoefficientKernelProd ℤ integerRow integerWitness
    integerWitness_rightInverse

private theorem integerSplit_forward :
    integerSplit (integerRightKernel, 5) = ![-2, 3] := by
  rw [integerSplit, LinearEquiv.rightCoefficientKernelProd_apply]
  funext i
  fin_cases i <;> norm_num [integerRightKernel, integerKernelVector, integerWitness]

private theorem integerSplit_forward_originalRow :
    dotProductBilin ℤ ℤᵐᵒᵖ integerRow (![-2, 3]) = 5 := by
  rw [integerOriginalRow]
  norm_num

private theorem integerSplit_inverse :
    integerSplit.symm (![-2, 3]) = (integerRightKernel, (5 : ℤ)) := by
  simpa only [integerSplit_forward] using
    (integerSplit.symm_apply_apply (integerRightKernel, (5 : ℤ)))

private theorem integerSplit_inverse_originalRow :
    (integerSplit.symm (![-2, 3])).2 =
      dotProductBilin ℤ ℤᵐᵒᵖ integerRow (![-2, 3]) :=
  LinearEquiv.rightCoefficientKernelProd_symm_snd ℤ integerRow integerWitness
    integerWitness_rightInverse _

private theorem integerSplit_inverse_second :
    (integerSplit.symm (![-2, 3])).2 = 5 := by
  rw [integerSplit_inverse_originalRow, integerSplit_forward_originalRow]

private theorem integerSplit_inverse_first :
    (integerSplit.symm (![-2, 3])).1.1 = integerKernelVector := by
  rw [integerSplit_inverse]
  rfl

private theorem integerSplit_inverse_first_ne_zero :
    (integerSplit.symm (![-2, 3])).1.1 ≠ 0 := by
  rw [integerSplit_inverse_first]
  exact integerKernelVector_ne_zero

private def integerCommutativeKernel :
    LinearMap.ker (Bass.coefficientRowScalarMap ℤ 2 integerRow) :=
  ⟨integerKernelVector,
    (LinearMap.mem_ker_coefficientRowScalarMap_iff_mem_ker_dotProductBilin
      ℤ integerRow integerKernelVector).mpr integerKernelVector_mem_ker⟩

private theorem integerTransport_forward :
    (LinearMap.coefficientRowKernelAddEquiv ℤ integerRow integerCommutativeKernel).1 =
      integerKernelVector :=
  (LinearMap.coefficientRowKernelAddEquiv_apply ℤ integerRow integerCommutativeKernel).trans rfl

private theorem integerTransport_inverse :
    ((LinearMap.coefficientRowKernelAddEquiv ℤ integerRow).symm integerRightKernel).1 =
      integerKernelVector :=
  (LinearMap.coefficientRowKernelAddEquiv_symm_apply ℤ integerRow integerRightKernel).trans rfl

private theorem integerTransport_roundTrip :
    (LinearMap.coefficientRowKernelAddEquiv ℤ integerRow).symm
        (LinearMap.coefficientRowKernelAddEquiv ℤ integerRow integerCommutativeKernel) =
      integerCommutativeKernel :=
  (LinearMap.coefficientRowKernelAddEquiv ℤ integerRow).symm_apply_apply
    integerCommutativeKernel

private theorem integerTransport_twice_first :
    (LinearMap.coefficientRowKernelAddEquiv ℤ integerRow
        ((2 : ℤ) • integerCommutativeKernel)).1 0 = 6 := by
  rw [LinearMap.coefficientRowKernelAddEquiv_smul]
  change
    (LinearMap.coefficientRowKernelAddEquiv ℤ integerRow integerCommutativeKernel).1 0 *
      (2 : ℤ) = 6
  rw [integerTransport_forward]
  norm_num [integerKernelVector]

/-- The commutative and right-linear splittings are compared using the
commutative split's chosen witness, which need not reduce to `integerWitness`. -/
private theorem integerSplit_sameWitness :
    Bass.kernelProdEquivOfIsRightUnimodular ℤ 2 integerRow integerRow_unimodular
        (integerCommutativeKernel, 5) =
      LinearEquiv.rightCoefficientKernelProd ℤ integerRow
        (Classical.choose integerRow_unimodular)
        (by
          change (∑ i, integerRow i * Classical.choose integerRow_unimodular i) = 1
          exact Classical.choose_spec integerRow_unimodular)
        (LinearMap.coefficientRowKernelAddEquiv ℤ integerRow integerCommutativeKernel, 5) :=
  LinearEquiv.kernelProdEquivOfIsRightUnimodular_eq_rightCoefficientKernelProd
    ℤ integerRow integerRow_unimodular (integerCommutativeKernel, 5)

private theorem emptyZeroRingSection (y : ZMod 1) :
    LinearMap.rightCoefficientSection (ZMod 1) (Fin.elim0 : Fin 0 → ZMod 1) y =
      Fin.elim0 := by
  funext i
  exact Fin.elim0 i

private theorem matrixSection_values (y : Matrix (Fin 2) (Fin 2) ℤ) :
    LinearMap.rightCoefficientSection _ matrixWitness y = ![y, y] := by
  funext i
  fin_cases i <;> simp [matrixWitness, LinearMap.rightCoefficientSection_apply]

end StableRangeTests.RightCoefficientClient
