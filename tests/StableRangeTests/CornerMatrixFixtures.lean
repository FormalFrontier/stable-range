/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Abel

/-!
# Three-by-three idempotent-corner fixtures

Ordered matrix units exhibit noncentral idempotents and noncommuting pairs of
nonunits in their corners over any nontrivial coefficient ring.

## References

* Mathlib, `RingTheory.Idempotents` and `Data.Matrix.Basis`
  (idempotent corners and indexed matrix units).
-/

set_option warningAsError true

@[expose] public section

namespace StableRangeTests.CornerMatrixFixtures

universe u

variable (A : Type u) [Ring A]

abbrev MatrixRing := Matrix (Fin 3) (Fin 3) A

def p : MatrixRing A := Matrix.single 0 0 1
def n : MatrixRing A := Matrix.single 0 1 1
def r : MatrixRing A := Matrix.single 1 1 1
def e : MatrixRing A := p A + r A
def b : MatrixRing A := n A + r A

@[simp] theorem p_mul_p : p A * p A = p A := by simp [p]
@[simp] theorem p_mul_n : p A * n A = n A := by simp [p, n]
@[simp] theorem p_mul_r : p A * r A = 0 := by simp [p, r]
@[simp] theorem n_mul_p : n A * p A = 0 := by simp [n, p]
@[simp] theorem n_mul_n : n A * n A = 0 := by simp [n]
@[simp] theorem n_mul_r : n A * r A = n A := by simp [n, r]
@[simp] theorem r_mul_p : r A * p A = 0 := by simp [r, p]
@[simp] theorem r_mul_n : r A * n A = 0 := by simp [r, n]
@[simp] theorem r_mul_r : r A * r A = r A := by simp [r]

theorem e_idempotent : IsIdempotentElem (e A) := by
  change e A * e A = e A
  simp [e, mul_add, add_mul]

@[simp] theorem e_mul_p : e A * p A = p A := by simp [e, add_mul]
@[simp] theorem p_mul_e : p A * e A = p A := by simp [e, mul_add]
@[simp] theorem e_mul_n : e A * n A = n A := by simp [e, add_mul]
@[simp] theorem n_mul_e : n A * e A = n A := by simp [e, mul_add]
@[simp] theorem e_mul_r : e A * r A = r A := by simp [e, add_mul]
@[simp] theorem r_mul_e : r A * e A = r A := by simp [e, mul_add]
@[simp] theorem e_mul_b : e A * b A = b A := by simp [b, mul_add]
@[simp] theorem b_mul_e : b A * e A = b A := by simp [b, add_mul]

def pc : (e_idempotent A).Corner :=
  ⟨p A, (Subsemigroup.mem_corner_iff (e_idempotent A)).mpr ⟨e_mul_p A, p_mul_e A⟩⟩
def nc : (e_idempotent A).Corner :=
  ⟨n A, (Subsemigroup.mem_corner_iff (e_idempotent A)).mpr ⟨e_mul_n A, n_mul_e A⟩⟩
def rc : (e_idempotent A).Corner :=
  ⟨r A, (Subsemigroup.mem_corner_iff (e_idempotent A)).mpr ⟨e_mul_r A, r_mul_e A⟩⟩
def bc : (e_idempotent A).Corner :=
  ⟨b A, (Subsemigroup.mem_corner_iff (e_idempotent A)).mpr ⟨e_mul_b A, b_mul_e A⟩⟩

def cornerVal (element : (e_idempotent A).Corner) : MatrixRing A :=
  ((show Subsemigroup.corner (e A) from element) : MatrixRing A)

@[simp] theorem pc_val : cornerVal A (pc A) = p A := rfl
@[simp] theorem nc_val : cornerVal A (nc A) = n A := rfl
@[simp] theorem rc_val : cornerVal A (rc A) = r A := rfl
@[simp] theorem bc_val : cornerVal A (bc A) = b A := rfl

theorem p_mul_b : p A * b A = n A := by simp [b, mul_add]
theorem b_mul_p : b A * p A = 0 := by simp [b, add_mul]
theorem p_mul_sub : p A * (p A - n A) + b A * r A = e A := by
  simp only [b, e, mul_sub, add_mul, p_mul_p, p_mul_n, n_mul_r, r_mul_r]
  abel

theorem correction : b A - p A * (-e A) = e A + n A := by
  simp only [b, e, mul_neg, mul_add, p_mul_p, p_mul_r, add_zero, sub_neg_eq_add]
  abel

theorem correction_mul_inverse : (e A + n A) * (e A - n A) = e A := by
  simp [mul_sub, add_mul, (e_idempotent A).eq]

theorem inverse_mul_correction : (e A - n A) * (e A + n A) = e A := by
  simp [sub_mul, mul_add, (e_idempotent A).eq]

def offCorner : MatrixRing A := Matrix.single 0 2 1
def outside : MatrixRing A := Matrix.single 2 2 1

theorem e_mul_offCorner : e A * offCorner A = offCorner A := by
  simp [e, offCorner, add_mul, p, r]
theorem offCorner_mul_e : offCorner A * e A = 0 := by
  simp [e, offCorner, mul_add, p, r]
theorem correction_mul_outside : (e A + n A) * outside A = 0 := by
  simp [e, outside, add_mul, p, n, r]

theorem pc_mul_bc : pc A * bc A = nc A := by
  apply Subtype.ext
  change p A * b A = n A
  exact p_mul_b A

theorem bc_mul_pc : bc A * pc A = 0 := by
  apply Subtype.ext
  change b A * p A = 0
  exact b_mul_p A

theorem pair_right_witness : pc A * (pc A - nc A) + bc A * rc A = 1 := by
  apply Subtype.ext
  change p A * (p A - n A) + b A * r A = e A
  exact p_mul_sub A

theorem explicit_corner_correction : IsUnit (bc A - pc A * (-1)) := by
  apply isUnit_iff_exists.mpr
  refine ⟨1 - nc A, ?_, ?_⟩
  · apply Subtype.ext
    change (b A - p A * (-e A)) * (e A - n A) = e A
    rw [correction, correction_mul_inverse]
  · apply Subtype.ext
    change (e A - n A) * (b A - p A * (-e A)) = e A
    rw [correction, inverse_mul_correction]

variable [Nontrivial A]

theorem p_ne_zero : p A ≠ 0 := by
  intro h
  have hentry := congrArg (fun matrix : MatrixRing A => matrix 0 0) h
  simp [p] at hentry

theorem n_ne_zero : n A ≠ 0 := by
  intro h
  have hentry := congrArg (fun matrix : MatrixRing A => matrix 0 1) h
  simp [n] at hentry

theorem nc_ne_zero : nc A ≠ 0 := by
  intro h
  exact n_ne_zero A (congrArg (cornerVal A) h)

theorem r_ne_zero : r A ≠ 0 := by
  intro h
  have hentry := congrArg (fun matrix : MatrixRing A => matrix 1 1) h
  simp [r] at hentry

theorem offCorner_ne_zero : offCorner A ≠ 0 := by
  intro h
  have hentry := congrArg (fun matrix : MatrixRing A => matrix 0 2) h
  simp [offCorner] at hentry

theorem outside_ne_zero : outside A ≠ 0 := by
  intro h
  have hentry := congrArg (fun matrix : MatrixRing A => matrix 2 2) h
  simp [outside] at hentry

theorem e_noncentral : e A * offCorner A ≠ offCorner A * e A := by
  rw [e_mul_offCorner, offCorner_mul_e]
  exact offCorner_ne_zero A

theorem pair_noncommuting : pc A * bc A ≠ bc A * pc A := by
  rw [pc_mul_bc, bc_mul_pc]
  exact nc_ne_zero A

theorem pc_nonunit : ¬ IsUnit (pc A) := by
  have hproduct : pc A * rc A = 0 := by
    apply Subtype.ext
    change p A * r A = 0
    exact p_mul_r A
  intro hunit
  obtain ⟨inverse, _, hleft⟩ := isUnit_iff_exists.mp hunit
  have hzero : rc A = 0 := by
    calc
      rc A = 1 * rc A := (one_mul _).symm
      _ = (inverse * pc A) * rc A := by rw [hleft]
      _ = 0 := by rw [mul_assoc, hproduct, mul_zero]
  exact r_ne_zero A (congrArg (cornerVal A) hzero)

theorem bc_nonunit : ¬ IsUnit (bc A) := by
  have hproduct : bc A * pc A = 0 := by
    apply Subtype.ext
    change b A * p A = 0
    exact b_mul_p A
  intro hunit
  obtain ⟨inverse, _, hleft⟩ := isUnit_iff_exists.mp hunit
  have hzero : pc A = 0 := by
    calc
      pc A = 1 * pc A := (one_mul _).symm
      _ = (inverse * bc A) * pc A := by rw [hleft]
      _ = 0 := by rw [mul_assoc, hproduct, mul_zero]
  exact p_ne_zero A (congrArg (cornerVal A) hzero)

theorem explicit_ambient_nonunit :
    ¬ IsUnit (cornerVal A (bc A - pc A * (-1))) := by
  have hval : cornerVal A (bc A - pc A * (-1)) = b A - p A * (-e A) := rfl
  rw [hval]
  rw [correction]
  intro hunit
  obtain ⟨inverse, _, hleft⟩ := isUnit_iff_exists.mp hunit
  have hzero : outside A = 0 := by
    calc
      outside A = 1 * outside A := (one_mul _).symm
      _ = (inverse * (e A + n A)) * outside A := by rw [hleft]
      _ = 0 := by rw [mul_assoc, correction_mul_outside, mul_zero]
  exact outside_ne_zero A hzero

end StableRangeTests.CornerMatrixFixtures
