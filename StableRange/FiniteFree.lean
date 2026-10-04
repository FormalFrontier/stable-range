/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.RowKernel
public import StableRange.BassDimension

/-!
# Cancellation of a finite free summand

A sufficiently large finite free module remains free after cancelling a finite
free summand from an explicit presentation. The number of remaining coordinates
is retained, even if the coefficient ring is the zero ring.

The exact-size formulation refines freeness for an explicit presentation: it
does not assert independence of the rank of different presentations.

## References

* C. Weibel, *The K-book* (2013), I.1.3, for finite stable presentations and
  stable-range cancellation.
* Prism, exact-size finite-stable-presentation cancellation design, for the
  coordinate-count formulation.
* Formal Frontier, Stable Range, `StableRange.RowKernel`, for the explicit
  stable-range equivalence of a unimodular row kernel.
* Mathlib, `Mathlib.LinearAlgebra.Pi` and `Mathlib.LinearAlgebra.FreeModule.Basic`,
  for finite free modules and linear equivalences.
-/

set_option warningAsError true

@[expose] public section

namespace Module

universe u v

variable (R : Type u) [CommRing R] (P : Type v)
  [AddCommGroup P] [Module R P]

/-- Cancel a finite free summand from an explicit stable presentation, provided
the remaining number of coordinates is at least the stable range. Inspired by
Weibel, *The K-book*, I.1.3, this exact-size formulation also includes the zero
ring and imposes no freeness assumption on `P`. -/
noncomputable def finLinearEquivOfStableRangeCondition
    {s n m : ℕ} (hs : Bass.StableRangeCondition R s) (hsn : s ≤ n)
    (e : (P × (Fin m → R)) ≃ₗ[R] (Fin (n + m) → R)) :
    P ≃ₗ[R] (Fin n → R) := by
  let peel (A : Type (max u v)) [AddCommGroup A] [Module R A]
      (k : ℕ) (hstable : Bass.StableRangeCondition R k)
      (step : (A × R) ≃ₗ[R] (Fin (k + 1) → R)) :
      A ≃ₗ[R] (Fin k → R) := by
    classical
    let projection : (A × R) →ₗ[R] R := LinearMap.snd R A R
    let transported : (Fin (k + 1) → R) →ₗ[R] R :=
      projection.comp step.symm.toLinearMap
    let row : Fin (k + 1) → R := fun i ↦ transported (Pi.single i 1)
    have hrow : Bass.coefficientRowScalarMap R (k + 1) row = transported := by
      apply LinearMap.ext
      intro x
      change row ⬝ᵥ x = transported x
      calc
        row ⬝ᵥ x = ∑ i, row i * x i := rfl
        _ = ∑ i, transported (Pi.single i (x i)) := by
          apply Finset.sum_congr rfl
          intro i _
          have hsingle : Pi.single i (x i) = x i • Pi.single i (1 : R) := by
            rw [← Pi.single_smul', smul_eq_mul, mul_one]
          rw [hsingle, map_smul, smul_eq_mul, mul_comm]
        _ = transported x := by rw [← map_sum, Finset.univ_sum_single]
    have hunimodular : Bass.IsRightUnimodular row := by
      refine ⟨step (0, 1), ?_⟩
      change Bass.coefficientRowScalarMap R (k + 1) row (step (0, 1)) = 1
      rw [hrow]
      simp [transported, projection]
    let kerProjection : LinearMap.ker projection ≃ₗ[R] A := {
      toFun x := x.1.1
      invFun x := ⟨(x, 0), by simp [LinearMap.mem_ker, projection]⟩
      left_inv x := by
        apply Subtype.ext
        have hx : x.1.2 = 0 := x.2
        exact Prod.ext rfl hx.symm
      right_inv x := rfl
      map_add' x y := rfl
      map_smul' r x := rfl
    }
    let kerTransport := Bass.kernelEquivOfLinearEquiv projection
      (Bass.coefficientRowScalarMap R (k + 1) row) step (fun x ↦ by
        rw [hrow]
        simp [transported, projection])
    exact kerProjection.symm |>.trans kerTransport |>.trans
      ((LinearEquiv.ofEq _ _
        (Bass.ker_coefficientRowScalarMap_eq R (k + 1) row)).trans
        (Bass.coefficientRowKernelEquivSuccOfStableRangeCondition
          R k hstable row hunimodular))
  induction m with
  | zero =>
      simpa only [Nat.add_zero] using
        (LinearEquiv.prodUnique (R := R) (M := P) (M₂ := Fin 0 → R)).symm.trans e
  | succ m ih =>
      let rebracket : ((P × (Fin m → R)) × R) ≃ₗ[R]
          (P × (Fin (m + 1) → R)) :=
        (LinearEquiv.prodAssoc R P (Fin m → R) R).trans
          ((LinearEquiv.refl R P).prodCongr
            ((LinearEquiv.prodComm R (Fin m → R) R).trans
              (Fin.consLinearEquiv R (fun _ : Fin (m + 1) ↦ R))))
      let lastCoordinate : ((P × (Fin m → R)) × R) ≃ₗ[R]
          (Fin ((n + m) + 1) → R) := by
        simpa only [Nat.add_succ] using rebracket.trans e
      have hnm : s ≤ n + m := le_trans hsn (Nat.le_add_right n m)
      exact ih (peel (P × (Fin m → R)) (n + m)
        (Bass.stableRangeCondition_mono hnm hs) lastCoordinate)

namespace Free

/-- A sufficiently large finite stable presentation makes its module free.
This is the freeness conclusion of Weibel, *The K-book*, I.1.3, in a
stable-range and exact-coordinate form. -/
theorem of_finProdEquiv_of_stableRangeCondition
    {s n m : ℕ} (hs : Bass.StableRangeCondition R s) (hsn : s ≤ n)
    (e : (P × (Fin m → R)) ≃ₗ[R] (Fin (n + m) → R)) :
    Module.Free R P :=
  Module.Free.of_equiv
    (Module.finLinearEquivOfStableRangeCondition R P hs hsn e).symm

end Free

/-- Cancel a finite free summand when a noetherian Krull-dimension upper bound
is strictly smaller than the number of remaining coordinates. -/
noncomputable def finLinearEquivOfKrullDimLE
    {d n m : ℕ} [IsNoetherianRing R] [Ring.KrullDimLE d R]
    (hdn : d + 1 ≤ n)
    (e : (P × (Fin m → R)) ≃ₗ[R] (Fin (n + m) → R)) :
    P ≃ₗ[R] (Fin n → R) :=
  finLinearEquivOfStableRangeCondition R P
    (Bass.stableRangeCondition_succ_of_krullDimLE (R := R) (d := d)) hdn e

namespace Free

/-- A finite stable presentation beyond a noetherian Krull-dimension bound
makes its module free, as in Weibel, *The K-book*, I.1.3. The bound need not
equal the ring's Krull dimension. -/
theorem of_finProdEquiv_of_krullDimLE
    {d n m : ℕ} [IsNoetherianRing R] [Ring.KrullDimLE d R]
    (hdn : d + 1 ≤ n)
    (e : (P × (Fin m → R)) ≃ₗ[R] (Fin (n + m) → R)) :
    Module.Free R P :=
  Module.Free.of_equiv (Module.finLinearEquivOfKrullDimLE R P hdn e).symm

end Free
end Module
