/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Basic
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi

/-!
# Coefficient rows and their kernels

This file relates finite right-unimodular rows to surjective linear maps on
finite free modules. It gives the explicit two-shear passage from Bass stable
range to freeness of sufficiently long row kernels. It also identifies the
kernel of a row in an explicitly invertible matrix with the free module on the
complementary column indices.
-/

set_option warningAsError true

@[expose] public section

open Function
open scoped Matrix

namespace Bass

universe u

/-- A finite coefficient row, regarded as a one-row matrix. -/
def coefficientRowMatrix (R : Type u) (n : ℕ) (a : Fin n → R) :
    Matrix (Fin 1) (Fin n) R :=
  fun _ j ↦ a j

/-- The linear functional represented by a finite coefficient row. -/
def coefficientRowLinearMap (R : Type u) [CommRing R]
    (n : ℕ) (a : Fin n → R) :
    (Fin n → R) →ₗ[R] (Fin 1 → R) :=
  (coefficientRowMatrix R n a).mulVecLin

theorem coefficientRowLinearMap_apply
    (R : Type u) [CommRing R] (n : ℕ) (a x : Fin n → R) :
    (coefficientRowLinearMap R n a x) 0 = a ⬝ᵥ x := by
  rfl

/-- A finite row is right-unimodular exactly when its coefficient functional
onto one copy of the ring is surjective. -/
theorem isRightUnimodular_iff_surjective_coefficientRowLinearMap
    (R : Type u) [CommRing R] (n : ℕ) (a : Fin n → R) :
    IsRightUnimodular a ↔ Function.Surjective (coefficientRowLinearMap R n a) := by
  classical
  constructor
  · rintro ⟨b, hb⟩ y
    refine ⟨y 0 • b, ?_⟩
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rw [coefficientRowLinearMap_apply, dotProduct_smul]
    change a ⬝ᵥ b = 1 at hb
    rw [hb]
    simp
  · intro hf
    let one : Fin 1 → R := fun _ ↦ 1
    obtain ⟨b, hb⟩ := hf one
    refine ⟨b, ?_⟩
    change a ⬝ᵥ b = 1
    have h := congrFun hb 0
    rw [coefficientRowLinearMap_apply] at h
    simpa [one] using h

/-- The scalar-valued version of a coefficient row. -/
def coefficientRowScalarMap (R : Type u) [CommRing R]
    (n : ℕ) (a : Fin n → R) : (Fin n → R) →ₗ[R] R :=
  (LinearMap.proj 0).comp (coefficientRowLinearMap R n a)

@[simp]
theorem coefficientRowScalarMap_apply
    (R : Type u) [CommRing R] (n : ℕ) (a x : Fin n → R) :
    coefficientRowScalarMap R n a x = a ⬝ᵥ x := by
  rfl

theorem ker_coefficientRowScalarMap_eq
    (R : Type u) [CommRing R] (n : ℕ) (a : Fin n → R) :
    LinearMap.ker (coefficientRowScalarMap R n a) =
      LinearMap.ker (coefficientRowLinearMap R n a) := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hx
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact hx
  · intro hx
    exact congrFun hx 0

/-- A split coefficient row, with its leading coordinate separated from its
tail. -/
def coefficientRowConsMap (R : Type u) [CommRing R]
    (n : ℕ) (a₀ : R) (a : Fin n → R) :
    (R × (Fin n → R)) →ₗ[R] R :=
  (LinearMap.lsmul R R a₀).comp (LinearMap.fst R R (Fin n → R)) +
    (coefficientRowScalarMap R n a).comp (LinearMap.snd R R (Fin n → R))

@[simp]
theorem coefficientRowConsMap_apply
    (R : Type u) [CommRing R] (n : ℕ) (a₀ : R) (a : Fin n → R)
    (x : R × (Fin n → R)) :
    coefficientRowConsMap R n a₀ a x = a₀ * x.1 + a ⬝ᵥ x.2 := by
  rfl

/-- Transporting the domain of a linear map by a linear equivalence transports
its kernel.  This explicit form is convenient when the conjugacy is proved
pointwise rather than as an equality of bundled maps. -/
noncomputable def kernelEquivOfLinearEquiv
    {R A B C : Type*} [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] C) (g : B →ₗ[R] C) (e : A ≃ₗ[R] B)
    (h : ∀ x, g (e x) = f x) : LinearMap.ker f ≃ₗ[R] LinearMap.ker g where
  toFun x := ⟨e x.1, by
    rw [LinearMap.mem_ker, h]
    exact LinearMap.mem_ker.mp x.2⟩
  invFun y := ⟨e.symm y.1, by
    rw [LinearMap.mem_ker, ← h]
    simp [LinearMap.mem_ker.mp y.2]⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by simp
  map_smul' r x := by simp

/-- The coordinate hyperplane where the `i`th coordinate vanishes is the
function module on the remaining indices. This specializes mathlib's
equivalence for intersections of kernels of coordinate projections. -/
noncomputable def coordinateHyperplaneEquiv
    (R : Type u) [Semiring R] (n : ℕ) (i : Fin n) :
    LinearMap.ker (LinearMap.proj i : (Fin n → R) →ₗ[R] R) ≃ₗ[R]
      ({j : Fin n // j ≠ i} → R) := by
  classical
  let e := LinearMap.iInfKerProjEquiv R (fun _ : Fin n ↦ R)
    (I := {j | j ≠ i}) (J := {i})
    (by
      rw [Set.disjoint_left]
      intro j hjI hjJ
      exact hjI (Set.mem_singleton_iff.mp hjJ))
    (by
      intro j _
      by_cases h : j = i
      · exact Or.inr (Set.mem_singleton_iff.mpr h)
      · exact Or.inl h)
  exact (LinearEquiv.ofEq _ _ (by simp)).trans e

/-- If `A` has the specified two-sided inverse `B` and its `i`th row is `a`,
then the kernel of the coefficient row `a` is explicitly equivalent to the
free module on the column indices other than `i`. -/
noncomputable def coefficientRowKernelEquivOfMatrixInverse
    (R : Type u) [CommRing R] (n : ℕ) (i : Fin n) (a : Fin n → R)
    (A B : Matrix (Fin n) (Fin n) R) (hrow : A i = a)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    LinearMap.ker (coefficientRowLinearMap R n a) ≃ₗ[R]
      ({j : Fin n // j ≠ i} → R) := by
  let matrixEquiv : (Fin n → R) ≃ₗ[R] (Fin n → R) :=
    LinearEquiv.ofLinearMap A.mulVecLin B.mulVecLin
      (by rw [← Matrix.mulVecLin_mul, hAB, Matrix.mulVecLin_one])
      (by rw [← Matrix.mulVecLin_mul, hBA, Matrix.mulVecLin_one])
  have hmatrix (x : Fin n → R) :
      (LinearMap.proj i : (Fin n → R) →ₗ[R] R) (matrixEquiv x) =
        coefficientRowScalarMap R n a x := by
    change A i ⬝ᵥ x = a ⬝ᵥ x
    rw [hrow]
  let kerEquiv := kernelEquivOfLinearEquiv
    (coefficientRowScalarMap R n a)
    (LinearMap.proj i : (Fin n → R) →ₗ[R] R)
    matrixEquiv hmatrix
  exact (LinearEquiv.ofEq _ _
      (ker_coefficientRowScalarMap_eq R n a).symm).trans
    (kerEquiv.trans (coordinateHyperplaneEquiv R n i))

/-- A coefficient row occurring as any distinguished row of an explicitly
invertible square matrix has free kernel. -/
theorem free_ker_coefficientRowLinearMap_of_matrix_inverse
    (R : Type u) [CommRing R] (n : ℕ) (i : Fin n) (a : Fin n → R)
    (A B : Matrix (Fin n) (Fin n) R) (hrow : A i = a)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    Module.Free R (LinearMap.ker (coefficientRowLinearMap R n a)) :=
  Module.Free.of_equiv
    (coefficientRowKernelEquivOfMatrixInverse
      R n i a A B hrow hAB hBA).symm

/-- The usual split-kernel equivalence for a map with a specified right
inverse. -/
noncomputable def kernelProdEquivOfRightInverse
    {R A B : Type*} [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (g : B →ₗ[R] A)
    (hfg : f.comp g = LinearMap.id) :
    (LinearMap.ker f × B) ≃ₗ[R] A := by
  let φ : (LinearMap.ker f × B) →ₗ[R] A :=
    (LinearMap.ker f).subtype.coprod g
  have hfg' (b : B) : f (g b) = b := by
    have h := LinearMap.congr_fun hfg b
    simpa using h
  let kproj : A →ₗ[R] LinearMap.ker f :=
    LinearMap.codRestrict (LinearMap.ker f) (LinearMap.id - g.comp f) fun a ↦ by
      simp [LinearMap.mem_ker, hfg']
  let ψ : A →ₗ[R] (LinearMap.ker f × B) := kproj.prod f
  exact LinearEquiv.ofLinearMap φ ψ
    (by ext a; simp [φ, ψ, kproj])
    (by ext p <;> simp [φ, ψ, kproj, hfg'])

/-- A right-unimodular coefficient row has the standard split presentation of
its kernel. -/
noncomputable def kernelProdEquivOfIsRightUnimodular
    (R : Type u) [CommRing R] (n : ℕ) (a : Fin n → R)
    (ha : IsRightUnimodular a) :
    (LinearMap.ker (coefficientRowScalarMap R n a) × R) ≃ₗ[R]
      (Fin n → R) := by
  let b := Classical.choose ha
  let g : R →ₗ[R] (Fin n → R) :=
    LinearMap.toSpanSingleton R (Fin n → R) b
  have hfg : (coefficientRowScalarMap R n a).comp g = LinearMap.id := by
    apply LinearMap.ext
    intro r
    change a ⬝ᵥ (r • b) = r
    rw [dotProduct_smul]
    have hb : a ⬝ᵥ b = 1 := Classical.choose_spec ha
    rw [hb]
    simp
  exact kernelProdEquivOfRightInverse (coefficientRowScalarMap R n a) g hfg

/-- The explicit two-shear equivalence from the kernel of a right-unimodular
split row to the shortened finite free module. The first shear replaces the
tail by the stable-reduced row, and the second uses a unimodular witness for
that row to kill the leading coefficient. -/
noncomputable def coefficientRowConsKernelEquivOfStableRangeCondition
    (R : Type u) [CommRing R] (n : ℕ)
    (hstable : StableRangeCondition R n) (a₀ : R) (a : Fin n → R)
    (ha : IsRightUnimodularCons a₀ a) :
    LinearMap.ker (coefficientRowConsMap R n a₀ a) ≃ₗ[R] (Fin n → R) := by
  classical
  let t := Classical.choose (hstable a₀ a ha)
  have hq := Classical.choose_spec (hstable a₀ a ha)
  let q : Fin n → R := fun i ↦ a i - a₀ * t i
  let b := Classical.choose hq
  let tdot := coefficientRowScalarMap R n t
  let leadToTail : R →ₗ[R] (Fin n → R) :=
    LinearMap.toSpanSingleton R (Fin n → R) (fun i ↦ a₀ * b i)
  let firstShear : (R × (Fin n → R)) ≃ₗ[R] (R × (Fin n → R)) :=
    (LinearEquiv.prodComm R R (Fin n → R)).trans
      (((LinearEquiv.refl R (Fin n → R)).skewProd
        (LinearEquiv.refl R R) tdot).trans
          (LinearEquiv.prodComm R (Fin n → R) R))
  let secondShear : (R × (Fin n → R)) ≃ₗ[R] (R × (Fin n → R)) :=
    (LinearEquiv.refl R R).skewProd
      (LinearEquiv.refl R (Fin n → R)) leadToTail
  let shear := firstShear.trans secondShear
  let reduced : (R × (Fin n → R)) →ₗ[R] R :=
    (coefficientRowScalarMap R n q).comp
      (LinearMap.snd R R (Fin n → R))
  have hshear (x : R × (Fin n → R)) :
      reduced (shear x) = coefficientRowConsMap R n a₀ a x := by
    change q ⬝ᵥ (x.2 + (x.1 + t ⬝ᵥ x.2) • (fun i ↦ a₀ * b i)) =
      a₀ * x.1 + a ⬝ᵥ x.2
    have hb : q ⬝ᵥ b = 1 := Classical.choose_spec hq
    have hc : q ⬝ᵥ (fun i ↦ a₀ * b i) = a₀ := by
      change q ⬝ᵥ (a₀ • b) = a₀
      rw [dotProduct_smul, hb]
      simp
    have hqx : q ⬝ᵥ x.2 = a ⬝ᵥ x.2 - a₀ * (t ⬝ᵥ x.2) := by
      change (fun i ↦ a i - a₀ * t i) ⬝ᵥ x.2 = _
      change (a - a₀ • t) ⬝ᵥ x.2 = _
      rw [sub_dotProduct, smul_dotProduct]
      rfl
    rw [dotProduct_add, dotProduct_smul, hc, hqx]
    ring
  let kerShear : LinearMap.ker (coefficientRowConsMap R n a₀ a) ≃ₗ[R]
      LinearMap.ker reduced :=
    kernelEquivOfLinearEquiv _ _ shear hshear
  let reducedKer : LinearMap.ker reduced ≃ₗ[R]
      (R × LinearMap.ker (coefficientRowScalarMap R n q)) := {
    toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
    invFun x := ⟨(x.1, x.2.1), x.2.2⟩
    left_inv x := rfl
    right_inv x := rfl
    map_add' x y := rfl
    map_smul' r x := rfl
  }
  let split := kernelProdEquivOfIsRightUnimodular R n q hq
  let freeModel : (Fin n → R) ≃ₗ[R]
      (R × LinearMap.ker (coefficientRowScalarMap R n q)) :=
    split.symm.trans (LinearEquiv.prodComm R _ _)
  exact (kerShear.trans reducedKer).trans freeModel.symm

/-- Bass stable range turns a right-unimodular split row into a kernel which is
free. -/
theorem free_ker_coefficientRowConsMap_of_stableRangeCondition
    (R : Type u) [CommRing R] (n : ℕ)
    (hstable : StableRangeCondition R n) (a₀ : R) (a : Fin n → R)
    (ha : IsRightUnimodularCons a₀ a) :
    Module.Free R (LinearMap.ker (coefficientRowConsMap R n a₀ a)) :=
  Module.Free.of_equiv
    (coefficientRowConsKernelEquivOfStableRangeCondition
      R n hstable a₀ a ha).symm

/-- At the literal stable-range length, the kernel of a right-unimodular
coefficient row is explicitly equivalent to the shortened finite free
module. -/
noncomputable def coefficientRowKernelEquivSuccOfStableRangeCondition
    (R : Type u) [CommRing R] (n : ℕ)
    (hstable : StableRangeCondition R n) (a : Fin (n + 1) → R)
    (ha : IsRightUnimodular a) :
    LinearMap.ker (coefficientRowLinearMap R (n + 1) a) ≃ₗ[R]
      (Fin n → R) := by
  let split : (R × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R) :=
    Fin.consLinearEquiv R (fun _ : Fin (n + 1) ↦ R)
  have hcons : IsRightUnimodularCons (a 0) (fun i ↦ a i.succ) :=
    (isRightUnimodular_finSucc_iff a).mp ha
  have hsplit (x : R × (Fin n → R)) :
      coefficientRowScalarMap R (n + 1) a (split x) =
        coefficientRowConsMap R n (a 0) (fun i ↦ a i.succ) x := by
    change a ⬝ᵥ Fin.cons x.1 x.2 = a 0 * x.1 + (fun i ↦ a i.succ) ⬝ᵥ x.2
    simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  let kerSplit := kernelEquivOfLinearEquiv
    (coefficientRowConsMap R n (a 0) (fun i ↦ a i.succ))
    (coefficientRowScalarMap R (n + 1) a) split hsplit
  exact (LinearEquiv.ofEq _ _
      (ker_coefficientRowScalarMap_eq R (n + 1) a).symm).trans
    (kerSplit.symm.trans
      (coefficientRowConsKernelEquivOfStableRangeCondition
        R n hstable (a 0) (fun i ↦ a i.succ) hcons))

/-- At the literal stable-range length, the kernel of a right-unimodular
coefficient row is free. -/
theorem free_ker_coefficientRowLinearMap_succ_of_stableRangeCondition
    (R : Type u) [CommRing R] (n : ℕ)
    (hstable : StableRangeCondition R n) (a : Fin (n + 1) → R)
    (ha : IsRightUnimodular a) :
    Module.Free R (LinearMap.ker (coefficientRowLinearMap R (n + 1) a)) :=
  Module.Free.of_equiv
    (coefficientRowKernelEquivSuccOfStableRangeCondition
      R n hstable a ha).symm

/-- If `(S_s)` holds, every right-unimodular coefficient row of length at
least `s + 1` has free kernel. -/
theorem free_ker_coefficientRowLinearMap_of_stableRangeCondition
    (R : Type u) [CommRing R] (s n : ℕ)
    (hstable : StableRangeCondition R s) (a : Fin n → R)
    (ha : IsRightUnimodular a) (hn : s + 1 ≤ n) :
    Module.Free R (LinearMap.ker (coefficientRowLinearMap R n a)) := by
  cases n with
  | zero => omega
  | succ m =>
      have hsm : s ≤ m := by omega
      exact free_ker_coefficientRowLinearMap_succ_of_stableRangeCondition
        R m (stableRangeCondition_mono hsm hstable) a ha

end Bass
