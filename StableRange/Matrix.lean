/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Regular
public import StableRange.Corner
public import Mathlib.Data.Matrix.Basic
public import GeneralLinearGroups.MatrixCorner
public import GeneralLinearGroups.RectangularBlockUnits
public import GeneralLinearGroups.UnitPivotDiagonalization

/-!
# Stable range one for finite matrix rings

Bass's stable-range-one condition passes from any ring to its finite square
matrix rings, including matrices indexed by the empty type. For nonempty finite
indices, the matrix ring satisfies stable range one exactly when the coefficient
ring does.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Exercise I.1.5 (Bass's stable-range condition); the finite-matrix
  preservation and reflection proofs here do not claim to follow that exercise.
* `general-linear-groups`, `MatrixCorner`, `RectangularBlockUnits` and
  `UnitPivotDiagonalization` (formalized entry/corner equivalence and ordered
  block units used in matrix reduction).
-/

@[expose] public section

universe u v

namespace Bass

open scoped Matrix

private theorem vecMul_upper {R : Type u} [Ring R] {n : ℕ}
    (r : (Fin 1 ⊕ Fin n) → R) (C : Matrix (Fin 1) (Fin n) R) :
    r ᵥ* (Matrix.GeneralLinearGroup.rectangularUpperUnit C :
      Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) =
      Sum.elim (r ∘ Sum.inl)
        (fun j ↦ r (Sum.inr j) + r (Sum.inl 0) * C 0 j) := by
  rw [Matrix.GeneralLinearGroup.rectangularUpperUnit_val, Matrix.vecMul_fromBlocks]
  funext j
  rcases j with j | j
  · simp
  · simp only [Sum.elim_inr, Pi.add_apply, Matrix.vecMul_one, Function.comp_apply]
    rw [add_comm ((r ∘ Sum.inl ᵥ* C) j) (r (Sum.inr j))]
    congr 1
    rw [Matrix.vecMul_apply]
    change (∑ i : Fin 1, r (Sum.inl i) * C i j) = _
    simp only [Fin.sum_univ_one]

private theorem vecMul_lower {R : Type u} [Ring R] {n : ℕ}
    (r : (Fin 1 ⊕ Fin n) → R) (C : Matrix (Fin n) (Fin 1) R) :
    r ᵥ* (Matrix.GeneralLinearGroup.rectangularLowerUnit C :
      Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) =
      Sum.elim (fun _ ↦ r (Sum.inl 0) + ∑ i, r (Sum.inr i) * C i 0)
        (r ∘ Sum.inr) := by
  rw [Matrix.GeneralLinearGroup.rectangularLowerUnit_val, Matrix.vecMul_fromBlocks]
  funext j
  rcases j with j | j
  · have : j = 0 := Subsingleton.elim j 0
    subst j
    simp only [Sum.elim_inl, Pi.add_apply, Matrix.vecMul_one, Function.comp_apply]
    congr 1
  · simp

private theorem vecMul_diagonalPair {R : Type u} [Ring R] {n : ℕ}
    (r : (Fin 1 ⊕ Fin n) → R) (W : GL (Fin n) R) :
    r ᵥ* (Matrix.GeneralLinearGroup.diagonalPairUnit (1 : GL (Fin 1) R) W :
      Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) =
      Sum.elim (r ∘ Sum.inl) ((r ∘ Sum.inr) ᵥ* (W : Matrix (Fin n) (Fin n) R)) := by
  rw [Matrix.GeneralLinearGroup.diagonalPairUnit_val, Matrix.vecMul_fromBlocks]
  funext j
  rcases j with j | j <;> simp

private theorem adjust_first_row {R : Type u} [Ring R]
    {κ : Type v} [Fintype κ] {n : ℕ}
    (h : StableRangeCondition R 1) (p x : κ → R)
    (b y : Fin (n + 1) → R)
    (hrow : (∑ i, p i * x i) + ∑ j, b j * y j = 1) :
    ∃ T : Matrix κ (Fin (n + 1)) R,
      IsRightUnimodular (fun j ↦ b j + ∑ i, p i * T i j) := by
  have hs : StableRangeCondition R (n + 1) :=
    stableRangeCondition_mono (Nat.succ_le_succ (Nat.zero_le n)) h
  obtain ⟨t, ht⟩ := hs (∑ i, p i * x i) b ⟨1, y, by simpa using hrow⟩
  refine ⟨fun i j ↦ -(x i * t j), ?_⟩
  convert ht using 1
  funext j
  simp only [mul_neg, ← mul_assoc, Finset.sum_mul, Finset.sum_neg_distrib,
    sub_eq_add_neg]

private theorem complete_row_fin {R : Type u} [Ring R]
    (h : StableRangeCondition R 1) (n : ℕ) (r : Fin (n + 1) → R)
    (hr : IsRightUnimodular r) :
    ∃ V : GL (Fin (n + 1)) R,
      r ᵥ* (V : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
        fun j ↦ if j = 0 then 1 else 0 := by
  induction n with
  | zero =>
    obtain ⟨s, hs⟩ := hr
    have hmul : r 0 * s 0 = 1 := by simpa [Fin.sum_univ_one] using hs
    have hunit : IsUnit (r 0) :=
      isUnit_of_mul_eq_one_of_stableRangeCondition_one h hmul
    obtain ⟨unit, hu⟩ := hunit
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 1) (unit⁻¹), ?_⟩
    funext j
    fin_cases j
    change (∑ i : Fin 1, r i *
      (Matrix.GeneralLinearGroup.scalar (Fin 1) (unit⁻¹) :
        Matrix (Fin 1) (Fin 1) R) i 0) = 1
    simp only [Fin.sum_univ_one, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_apply, ite_true]
    rw [← hu]
    exact unit.mul_inv
  | succ n ih =>
    have hs : StableRangeCondition R (n + 1) :=
      stableRangeCondition_mono (Nat.succ_le_succ (Nat.zero_le n)) h
    obtain ⟨t, ht⟩ := hs (r 0) (fun i ↦ r i.succ)
      ((isRightUnimodular_finSucc_iff r).mp hr)
    obtain ⟨W, hW⟩ := ih (fun i ↦ r i.succ - r 0 * t i) ht
    let e := Matrix.firstRestEquiv (n + 1)
    let α := Fin 1 ⊕ Fin (n + 1)
    let r' : α → R := fun j ↦ r (e.symm j)
    let E : GL α R :=
      Matrix.GeneralLinearGroup.rectangularUpperUnit (fun _ j ↦ -t j)
    let D : GL α R :=
      Matrix.GeneralLinearGroup.diagonalPairUnit (1 : GL (Fin 1) R) W
    let L : GL α R :=
      Matrix.GeneralLinearGroup.rectangularLowerUnit
        (fun i _ ↦ if i = 0 then 1 - r 0 else 0)
    let F : GL α R :=
      Matrix.GeneralLinearGroup.rectangularUpperUnit
        (fun _ i ↦ if i = 0 then -1 else 0)
    have hE : r' ᵥ* (E : Matrix α α R) =
        Sum.elim (fun _ ↦ r 0) (fun i ↦ r i.succ - r 0 * t i) := by
      calc
        _ = Sum.elim (r' ∘ Sum.inl)
            (fun j ↦ r' (Sum.inr j) + r' (Sum.inl 0) * (-t j)) :=
          vecMul_upper r' (fun _ j ↦ -t j)
        _ = Sum.elim (fun _ ↦ r 0) (fun i ↦ r i.succ - r 0 * t i) := by
          funext j
          rcases j with j | j
          · have hj : j = 0 := Subsingleton.elim j 0
            subst j
            simp [r', e, Matrix.firstRestEquiv_symm_inl]
          · simp [r', e, Matrix.firstRestEquiv_symm_inr, sub_eq_add_neg]
    have hD : (r' ᵥ* (E : Matrix α α R)) ᵥ* (D : Matrix α α R) =
        Sum.elim (fun _ ↦ r 0) (fun i : Fin (n + 1) ↦ if i = 0 then 1 else 0) := by
      rw [hE, show (D : Matrix α α R) =
        (Matrix.GeneralLinearGroup.diagonalPairUnit (1 : GL (Fin 1) R) W :
          Matrix α α R) from rfl, vecMul_diagonalPair]
      funext j
      rcases j with j | j
      · rfl
      · exact congrFun hW j
    have hL : ((r' ᵥ* (E : Matrix α α R)) ᵥ* (D : Matrix α α R)) ᵥ*
        (L : Matrix α α R) =
        Sum.elim (fun _ ↦ (1 : R))
          (fun i : Fin (n + 1) ↦ if i = 0 then 1 else 0) := by
      calc
        _ = (Sum.elim (fun _ ↦ r 0)
            (fun i : Fin (n + 1) ↦ if i = 0 then 1 else 0)) ᵥ*
              (L : Matrix α α R) := by rw [hD]
        _ = Sum.elim
            (fun _ ↦ r 0 + ∑ i : Fin (n + 1),
              (if i = 0 then 1 else 0) * (if i = 0 then 1 - r 0 else 0))
            (fun i : Fin (n + 1) ↦ if i = 0 then 1 else 0) :=
          vecMul_lower _ _
        _ = _ := by
          funext j
          rcases j with j | j
          · have hj : j = 0 := Subsingleton.elim j 0
            subst j
            simp [Finset.sum_ite_eq', sub_eq_add_neg]
          · rfl
    have hF : (((r' ᵥ* (E : Matrix α α R)) ᵥ* (D : Matrix α α R)) ᵥ*
        (L : Matrix α α R)) ᵥ* (F : Matrix α α R) =
        Sum.elim (fun _ ↦ (1 : R)) (fun _ : Fin (n + 1) ↦ 0) := by
      rw [hL]
      funext j
      have hAction := congrFun (vecMul_upper
        (Sum.elim (fun _ ↦ (1 : R))
          (fun i : Fin (n + 1) ↦ if i = 0 then 1 else 0))
        (fun (_ : Fin 1) (i : Fin (n + 1)) ↦ if i = 0 then -1 else 0)) j
      rcases j with j | j
      · simpa [F] using hAction
      · by_cases hj : j = 0 <;> simpa [F, hj] using hAction
    let U : GL α R := E * D * L * F
    have hU : r' ᵥ* (U : Matrix α α R) =
        Sum.elim (fun _ ↦ (1 : R)) (fun _ : Fin (n + 1) ↦ 0) := by
      simpa only [U, Units.val_mul, Matrix.vecMul_vecMul] using hF
    refine ⟨Matrix.GeneralLinearGroup.reindexEquiv R e.symm U, ?_⟩
    change r ᵥ* ((U : Matrix α α R).submatrix e e) = _
    rw [Matrix.submatrix_vecMul_equiv]
    change (r' ᵥ* (U : Matrix α α R)) ∘ e = _
    rw [hU]
    funext j
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · simp [e, Matrix.firstRestEquiv_zero]
    · simp [e, Matrix.firstRestEquiv_succ]

private theorem isUnit_of_upper_fin {R : Type u} [Ring R] {n : ℕ}
    (N : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h00 : N 0 0 = 1) (h10 : ∀ i : Fin n, N i.succ 0 = 0)
    (h22 : IsUnit (N.submatrix Fin.succ Fin.succ)) : IsUnit N := by
  obtain ⟨D, hD⟩ := h22
  let e := Matrix.firstRestEquiv n
  let B : Matrix (Fin 1) (Fin n) R := fun _ i ↦ N 0 i.succ
  let U : GL (Fin 1 ⊕ Fin n) R :=
    Matrix.GeneralLinearGroup.triangularUnit (1 : GL (Fin 1) R) B D
  have hblock : (Matrix.reindexRingEquiv R e) N =
      Matrix.fromBlocks 1 B 0 (D : Matrix (Fin n) (Fin n) R) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · have hi : i = 0 := Subsingleton.elim i 0
      have hj : j = 0 := Subsingleton.elim j 0
      subst i; subst j
      simpa [e, Matrix.firstRestEquiv_symm_inl] using h00
    · have hi : i = 0 := Subsingleton.elim i 0
      subst i
      simp [B, e, Matrix.fromBlocks, Matrix.firstRestEquiv_symm_inl,
        Matrix.firstRestEquiv_symm_inr]
    · have hj : j = 0 := Subsingleton.elim j 0
      subst j
      simpa [e, Matrix.firstRestEquiv_symm_inl, Matrix.firstRestEquiv_symm_inr] using h10 i
    · simpa [e, Matrix.firstRestEquiv_symm_inr] using
        congrArg (fun M : Matrix (Fin n) (Fin n) R ↦ M i j) hD.symm
  refine ⟨Matrix.GeneralLinearGroup.reindexEquiv R e.symm U, ?_⟩
  apply (Matrix.reindexRingEquiv R e).injective
  calc
    (Matrix.reindexRingEquiv R e)
        (Matrix.GeneralLinearGroup.reindexEquiv R e.symm U :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      (U : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) := by
        ext i j
        simp [Matrix.GeneralLinearGroup.reindexEquiv_apply]
    _ = Matrix.fromBlocks 1 B 0 (D : Matrix (Fin n) (Fin n) R) :=
      Matrix.GeneralLinearGroup.triangularUnit_val (1 : GL (Fin 1) R) B D
    _ = (Matrix.reindexRingEquiv R e) N := hblock.symm

private theorem split_change_basis {R : Type u} [Ring R]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {κ : Type*} [Fintype κ]
    (P : Matrix ι κ R) (Q : Matrix ι ι R)
    (X : Matrix κ ι R) (Y : Matrix ι ι R)
    (h : P * X + Q * Y = 1) (L V : GL ι R) :
    ((L : Matrix ι ι R) * P) * (X * ((L⁻¹ : GL ι R) : Matrix ι ι R)) +
      ((L : Matrix ι ι R) * Q * (V : Matrix ι ι R)) *
        (((V⁻¹ : GL ι R) : Matrix ι ι R) * Y *
          ((L⁻¹ : GL ι R) : Matrix ι ι R)) = 1 := by
  have hv : (V : Matrix ι ι R) * ((V⁻¹ : GL ι R) : Matrix ι ι R) = 1 := V.val_inv
  calc
    _ = (L : Matrix ι ι R) * (P * X + Q * Y) *
        ((L⁻¹ : GL ι R) : Matrix ι ι R) := by
      simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
      rw [← Matrix.mul_assoc (V : Matrix ι ι R)
        ((V⁻¹ : GL ι R) : Matrix ι ι R)
        (Y * ((L⁻¹ : GL ι R) : Matrix ι ι R)), hv, Matrix.one_mul]
    _ = 1 := by rw [h, Matrix.mul_one]; exact L.val_inv

private theorem clear_lower_column_fin {R : Type u} [Ring R] {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hrow : ∀ j, Q 0 j = if j = 0 then 1 else 0) :
    ∃ L : GL (Fin (n + 1)) R, ∃ C : Matrix (Fin n) (Fin n) R,
      (Matrix.reindexRingEquiv R (Matrix.firstRestEquiv n))
        ((L : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * Q) =
          Matrix.fromBlocks 1 0 0 C := by
  let e := Matrix.firstRestEquiv n
  let Q' := (Matrix.reindexRingEquiv R e) Q
  let B := Q'.toBlocks₂₁
  let C := Q'.toBlocks₂₂
  have h11 : Q'.toBlocks₁₁ = 1 := by
    ext i j
    have hi : i = 0 := Subsingleton.elim i 0
    have hj : j = 0 := Subsingleton.elim j 0
    subst i; subst j
    simpa [Q', e, Matrix.toBlocks₁₁, Matrix.submatrix_apply,
      Matrix.firstRestEquiv_symm_inl] using hrow 0
  have h12 : Q'.toBlocks₁₂ = 0 := by
    ext i j
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    simpa [Q', e, Matrix.toBlocks₁₂, Matrix.submatrix_apply,
      Matrix.firstRestEquiv_symm_inl,
      Matrix.firstRestEquiv_symm_inr] using hrow j.succ
  have hQ' : Q' = Matrix.fromBlocks 1 0 B C := by
    calc
      Q' = Matrix.fromBlocks Q'.toBlocks₁₁ Q'.toBlocks₁₂
          Q'.toBlocks₂₁ Q'.toBlocks₂₂ := (Matrix.fromBlocks_toBlocks Q').symm
      _ = Matrix.fromBlocks 1 0 B C := by rw [h11, h12]
  let L : GL (Fin (n + 1)) R :=
    Matrix.GeneralLinearGroup.reindexEquiv R e.symm
      (Matrix.GeneralLinearGroup.rectangularLowerUnit (-B))
  refine ⟨L, C, ?_⟩
  have hLe : (Matrix.reindexRingEquiv R e)
      (L : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      (Matrix.GeneralLinearGroup.rectangularLowerUnit (-B) :
        Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) := by
    ext i j
    simp [L, e, Matrix.GeneralLinearGroup.reindexEquiv_apply]
  calc
    (Matrix.reindexRingEquiv R e)
        ((L : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * Q) =
      (Matrix.GeneralLinearGroup.rectangularLowerUnit (-B) :
        Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) * Q' := by
          rw [map_mul, hLe]
    _ = Matrix.fromBlocks 1 0 0 C := by
      rw [hQ', Matrix.GeneralLinearGroup.rectangularLowerUnit_val,
        Matrix.fromBlocks_multiply]
      simp

private theorem split_bottom_fin {R : Type u} [Ring R] {κ : Type v} [Fintype κ]
    {n : ℕ} (P : Matrix (Fin (n + 1)) κ R)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (X : Matrix κ (Fin (n + 1)) R)
    (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hsplit : P * X + Q * Y = 1)
    (h10 : ∀ i : Fin n, Q i.succ 0 = 0) :
    P.submatrix Fin.succ id * X.submatrix id Fin.succ +
      Q.submatrix Fin.succ Fin.succ * Y.submatrix Fin.succ Fin.succ = 1 := by
  ext i j
  have hij := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) R ↦
    M i.succ j.succ) hsplit
  simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.submatrix_apply,
    Matrix.one_apply, Fin.succ_inj, Fin.sum_univ_succ, h10, zero_mul,
    id_eq,
    zero_add] using hij

private theorem rectangular_completion_fin {R : Type u} [Ring R]
    {κ : Type v} [Fintype κ] (h : StableRangeCondition R 1) :
    ∀ n (P : Matrix (Fin n) κ R) (Q : Matrix (Fin n) (Fin n) R)
      (X : Matrix κ (Fin n) R) (Y : Matrix (Fin n) (Fin n) R),
      P * X + Q * Y = 1 → ∃ T : Matrix κ (Fin n) R, IsUnit (Q + P * T) := by
  intro n
  induction n with
  | zero =>
    intro P Q X Y hsplit
    refine ⟨0, ?_⟩
    have hQ : Q = 1 := by ext i; exact i.elim0
    simp [hQ]
  | succ n ih =>
    intro P Q X Y hsplit
    have hfirst : (∑ i, P 0 i * X i 0) +
        ∑ j : Fin (n + 1), Q 0 j * Y j 0 = 1 := by
      have hij := congrArg
        (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) R ↦ M 0 0) hsplit
      simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply, ite_true] using hij
    obtain ⟨T0, hrow⟩ := adjust_first_row h (fun i ↦ P 0 i)
      (fun i ↦ X i 0) (fun j ↦ Q 0 j) (fun j ↦ Y j 0) hfirst
    let Q0 : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Q + P * T0
    let X0 : Matrix κ (Fin (n + 1)) R := X - T0 * Y
    have hsplit0 : P * X0 + Q0 * Y = 1 := by
      calc
        P * X0 + Q0 * Y = P * X + Q * Y := by
          dsimp only [X0, Q0]
          simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.mul_assoc]
          abel
        _ = 1 := hsplit
    have hrow0 : IsRightUnimodular (fun j ↦ Q0 0 j) := by
      simpa [Q0, Matrix.add_apply, Matrix.mul_apply] using hrow
    obtain ⟨V, hV⟩ := complete_row_fin h n (fun j ↦ Q0 0 j) hrow0
    let QV : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
      Q0 * (V : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    have hQV : ∀ j : Fin (n + 1), QV 0 j = if j = 0 then 1 else 0 := by
      intro j
      change ((fun i ↦ Q0 0 i) ᵥ*
        (V : Matrix (Fin (n + 1)) (Fin (n + 1)) R)) j = _
      exact congrFun hV j
    obtain ⟨L, C, hclear⟩ := clear_lower_column_fin QV hQV
    let P2 : Matrix (Fin (n + 1)) κ R :=
      (L : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * P
    let Q2 : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
      (L : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * QV
    let X2 : Matrix κ (Fin (n + 1)) R :=
      X0 * ((L⁻¹ : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    let Y2 : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
      ((V⁻¹ : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * Y *
        ((L⁻¹ : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    have hsplit2 : P2 * X2 + Q2 * Y2 = 1 := by
      simpa only [P2, Q2, QV, X2, Y2, Matrix.mul_assoc] using
        split_change_basis P Q0 X0 Y hsplit0 L V
    have h00 : Q2 0 0 = 1 := by
      have hij := congrArg
        (fun M : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R ↦
          M (Sum.inl 0) (Sum.inl 0)) hclear
      simpa [Q2, Matrix.firstRestEquiv_symm_inl] using hij
    have h10 : ∀ i : Fin n, Q2 i.succ 0 = 0 := by
      intro i
      have hij := congrArg
        (fun M : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R ↦
          M (Sum.inr i) (Sum.inl 0)) hclear
      simpa [Q2, Matrix.firstRestEquiv_symm_inl,
        Matrix.firstRestEquiv_symm_inr] using hij
    have hC : Q2.submatrix Fin.succ Fin.succ = C := by
      ext i j
      have hij := congrArg
        (fun M : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R ↦
          M (Sum.inr i) (Sum.inr j)) hclear
      simpa [Q2, Matrix.firstRestEquiv_symm_inr] using hij
    let Pb : Matrix (Fin n) κ R := P2.submatrix Fin.succ id
    let Xb : Matrix κ (Fin n) R := X2.submatrix id Fin.succ
    let Yb : Matrix (Fin n) (Fin n) R := Y2.submatrix Fin.succ Fin.succ
    have hsplitb : Pb * Xb + C * Yb = 1 := by
      have hs := split_bottom_fin P2 Q2 X2 Y2 hsplit2 h10
      rw [hC] at hs
      exact hs
    obtain ⟨T1, hunitb⟩ := ih Pb C Xb Yb hsplitb
    let E : Matrix κ (Fin (n + 1)) R := fun i ↦ Fin.cons 0 (T1 i)
    have hE0 (i : κ) : E i 0 = 0 := rfl
    have hEsucc (i : κ) (j : Fin n) : E i j.succ = T1 i j := rfl
    let N : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Q2 + P2 * E
    have hN00 : N 0 0 = 1 := by
      simp only [N, Matrix.add_apply, Matrix.mul_apply, hE0,
        mul_zero, Finset.sum_const_zero, add_zero]
      exact h00
    have hN10 : ∀ i : Fin n, N i.succ 0 = 0 := by
      intro i
      simp only [N, Matrix.add_apply, Matrix.mul_apply, hE0,
        mul_zero, Finset.sum_const_zero, add_zero]
      exact h10 i
    have hN22 : IsUnit (N.submatrix Fin.succ Fin.succ) := by
      have heq : N.submatrix Fin.succ Fin.succ = C + Pb * T1 := by
        ext i j
        simp only [N, Matrix.submatrix_apply, Matrix.add_apply,
          Matrix.mul_apply, hEsucc, Pb, id_eq]
        rw [← hC]
        simp only [Matrix.submatrix_apply]
      rw [heq]
      exact hunitb
    have hunitN : IsUnit N := isUnit_of_upper_fin N hN00 hN10 hN22
    let T : Matrix κ (Fin (n + 1)) R :=
      T0 + E * ((V⁻¹ : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    have hVi : ((V⁻¹ : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        (V : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = 1 := V.inv_val
    have hreturn : (L : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        (Q + P * T) * (V : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = N := by
      calc
        _ = (L : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * (Q + P * T0) *
              (V : Matrix (Fin (n + 1)) (Fin (n + 1)) R) + P2 * E := by
          simp only [T, P2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hVi,
            Matrix.mul_one]
          abel
        _ = N := by simp only [N, Q2, QV, Q0, P2, Matrix.mul_assoc]
    refine ⟨T, ?_⟩
    have hback : Q + P * T =
        ((L⁻¹ : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
          N * ((V⁻¹ : GL (Fin (n + 1)) R) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) R) := by
      calc
        Q + P * T =
            ((L⁻¹ : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
              ((L : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
                (Q + P * T) * (V : Matrix (Fin (n + 1)) (Fin (n + 1)) R)) *
              ((V⁻¹ : GL (Fin (n + 1)) R) :
                Matrix (Fin (n + 1)) (Fin (n + 1)) R) := by
                  simp [Matrix.mul_assoc]
        _ = _ := by rw [hreturn]
    rw [hback]
    exact ((Units.isUnit (L⁻¹)).mul hunitN).mul (Units.isUnit (V⁻¹))

/-- Finite square matrices over a ring satisfying `(S₁)` also satisfy `(S₁)`.
The block reduction uses `general-linear-groups`' rectangular block units;
the stable-range convention is as in Weibel, *The K-book*, Exercise I.1.5. -/
theorem stableRangeCondition_one_matrix
    {R : Type u} [Ring R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (h : StableRangeCondition R 1) :
    StableRangeCondition (Matrix ι ι R) 1 := by
  have hFin (n : ℕ) : StableRangeCondition (Matrix (Fin n) (Fin n) R) 1 := by
    apply (stableRangeCondition_one_iff_forall_isUnit_sub_mul).2
    intro A B hAB
    obtain ⟨X, Y, hXY⟩ := hAB
    obtain ⟨T, hT⟩ := rectangular_completion_fin h n A B X Y hXY
    refine ⟨-T, ?_⟩
    simpa only [mul_neg, sub_neg_eq_add] using hT
  exact (hFin (Fintype.card ι)).map_equiv
    (Matrix.reindexRingEquiv R (Fintype.equivFin ι)).symm

/-- For nonempty finite indices, the matrix ring satisfies `(S₁)` if and only if
its coefficient ring does. Reflection uses the diagonal matrix-unit corner
formalized in `general-linear-groups`' `MatrixCorner`. -/
theorem stableRangeCondition_one_matrix_iff
    {R : Type u} [Ring R] {ι : Type v} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    StableRangeCondition (Matrix ι ι R) 1 ↔ StableRangeCondition R 1 := by
  constructor
  · intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact (stableRangeCondition_one_corner
      (Matrix.isIdempotentElem_single_one (R := R) i) h).map_equiv
        (Matrix.singleCornerRingEquiv i)
  · exact stableRangeCondition_one_matrix

end Bass
