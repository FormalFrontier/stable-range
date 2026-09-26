/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import StableRange
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Ordinary public-import clients

Persistent private proofs exercise the advertised API without `import all`,
project-leaf imports or private implementation names. The extra Mathlib imports
supply `ZMod` fixtures and the Artinian dimension instance. These are regression
clients, not new public mathematical API or a complete release proof audit.
-/

set_option warningAsError true

namespace StableRangePublicAPIClient

universe u v w x y

section Rings

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

private theorem literal_condition (n : ℕ) :
    Bass.StableRangeCondition R n ↔
      ∀ r : Fin (n + 1) → R, Bass.IsRightUnimodular r →
        ∃ t : Fin n → R, Bass.IsRightUnimodular (fun i ↦ r i.succ - r 0 * t i) :=
  Bass.stableRangeCondition_iff_literal n

private theorem separate_row {n : ℕ} (r : Fin (n + 1) → R) :
    Bass.IsRightUnimodular r ↔ Bass.IsRightUnimodularCons (r 0) (fun i ↦ r i.succ) :=
  Bass.isRightUnimodular_finSucc_iff r

private theorem map_row (f : R →+* S) {n : ℕ} {r : Fin n → R}
    (h : Bass.IsRightUnimodular r) : Bass.IsRightUnimodular (fun i ↦ f (r i)) :=
  h.map f

private theorem monotone {m n : ℕ} (hmn : m ≤ n)
    (h : Bass.StableRangeCondition R m) : Bass.StableRangeCondition R n :=
  Bass.stableRangeCondition_mono hmn h

private theorem transport (e : R ≃+* S) (n : ℕ) :
    Bass.StableRangeCondition R n ↔ Bass.StableRangeCondition S n :=
  Bass.stableRangeCondition_equiv_iff e n

private theorem descend (f : R →+* S) (hf : Function.Surjective f) {n : ℕ}
    (h : Bass.StableRangeCondition R n) : Bass.StableRangeCondition S n :=
  Bass.stableRangeCondition_of_surjective f hf h

private theorem quotient_reflection (I : TwoSidedIdeal R) (hI : I.IsQuasiregular)
    (n : ℕ) : Bass.StableRangeCondition R n ↔
      Bass.StableRangeCondition (R ⧸ I.asIdeal) n :=
  Bass.stableRangeCondition_quotient_iff I hI n

private theorem quotient_zero {n : ℕ} (h : Bass.StableRangeCondition R n) :
    Bass.StableRangeCondition (R ⧸ (⊥ : TwoSidedIdeal R).asIdeal) n :=
  Bass.stableRangeCondition_quotient ⊥ h

private theorem local_condition [IsLocalRing R] : Bass.StableRangeCondition R 1 :=
  Bass.stableRangeCondition_one_of_isLocalRing

private theorem local_least [IsLocalRing R] : Bass.IsStableRange R 1 :=
  Bass.stableRange_one_of_isLocalRing

private theorem nontrivial_not_zero [Nontrivial R] : ¬ Bass.StableRangeCondition R 0 :=
  Bass.not_stableRangeCondition_zero

private theorem directly_finite (h : Bass.StableRangeCondition R 1) :
    IsDedekindFiniteMonoid R :=
  Bass.stableRangeCondition_one_isDedekindFinite h

private theorem regular_equivalence (h : Bass.IsVonNeumannRegular R) :
    Bass.IsUnitRegular R ↔ Bass.StableRangeCondition R 1 :=
  Bass.isUnitRegular_iff_stableRangeCondition_one h

private theorem right_ideal_complement {a z : R} (h : a = a * z * a) :
    IsCompl (Bass.principalRightIdeal a) (Bass.principalRightIdeal (1 - a * z)) :=
  Bass.principalRightIdeals_isCompl_of_innerInverse h

private theorem right_ideal_membership (a b : R) : b ∈ Bass.principalRightIdeal a ↔
    ∃ c : R, a * c = b :=
  Bass.mem_principalRightIdeal

end Rings

private theorem zero_ring_condition : Bass.StableRangeCondition (ZMod 1) 0 := by
  intro a r _
  refine ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i, ?_⟩
  exact Subsingleton.elim _ _

private theorem zero_ring_unit_regular : Bass.IsUnitRegular (ZMod 1) := by
  intro a
  exact ⟨1, Subsingleton.elim _ _⟩

private theorem shift_general (S : Type u) (M : Type v) [Semiring S]
    [AddCommGroup M] [Module S M] [Nontrivial M] :
    ¬ Bass.IsUnitRegular (Module.End S (ℕ →₀ M)) :=
  Bass.not_isUnitRegular_moduleEnd_finsupp_nat S M

private theorem shift_not_free_assumption :
    ¬ Bass.IsUnitRegular (Module.End ℕ (ℕ →₀ ℤ)) :=
  Bass.not_isUnitRegular_moduleEnd_finsupp_nat ℕ ℤ

section DivisionRings

variable {K : Type u} [DivisionRing K]
variable {V : Type v} [AddCommGroup V] [Module K V]

private theorem arbitrary_inner_inverse (f : Module.End K V) :
    ∃ g : Module.End K V, f = f * g * f :=
  f.exists_innerInverse

private theorem finite_automorphic_inverse [FiniteDimensional K V] (f : Module.End K V) :
    ∃ g : V ≃ₗ[K] V, ∀ v, f (g (f v)) = f v :=
  f.exists_linearEquiv_innerInverse

private theorem empty_matrix_unit_regular :
    Bass.IsUnitRegular (Matrix (Fin 0) (Fin 0) K) :=
  Bass.isUnitRegular_matrix

variable {m : Type v} {n : Type w} {p : Type x} {o : Type y}
variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable [Fintype p] [DecidableEq p] [Fintype o] [DecidableEq o]

omit [Fintype p] [DecidableEq p] in
private theorem row_rank_product (A : Matrix m n K) (B : Matrix n p K) :
    Matrix.rowRank (A * B) ≤ Matrix.rowRank A ∧
      Matrix.rowRank (A * B) ≤ Matrix.rowRank B :=
  ⟨Matrix.rowRank_mul_le_left A B, Matrix.rowRank_mul_le_right A B⟩

omit [Fintype n] [DecidableEq n] [Fintype o] [DecidableEq o] in
private theorem reindex_rank (er : m ≃ p) (ec : n ≃ o) (A : Matrix m n K) :
    Matrix.rowRank (A.reindex er ec) = Matrix.rowRank A :=
  Matrix.rowRank_reindex er ec A

omit [Fintype n] [DecidableEq n] in
private theorem block_rank (A : Matrix m n K) :
    Matrix.rowRank (Matrix.repeatBlock (o := o) A) =
      Fintype.card o * Matrix.rowRank A :=
  Matrix.rowRank_repeatBlock A

private theorem realize_rank (k : ℕ) (hk : k ≤ Fintype.card n) :
    ∃ A : Matrix n n K, Matrix.rowRank A = k :=
  Matrix.exists_rowRank_eq k hk

private theorem orthogonal_rank (E G : Matrix n n K)
    (hE : E * E = E) (hG : G * G = G) (hEG : E * G = 0) (hGE : G * E = 0) :
    Matrix.rowRank (E + G) = Matrix.rowRank E + Matrix.rowRank G :=
  Matrix.rowRank_add_of_orthogonal_idempotents E G hE hG hEG hGE

private theorem normalized_identity [Nonempty n] :
    Matrix.normalizedRowRank (1 : Matrix n n K) = 1 :=
  Matrix.normalizedRowRank_one

private theorem normalized_bounds [Nonempty n] (A : Matrix n n K) :
    Matrix.normalizedRowRank A ∈ Set.Icc (0 : ℝ) 1 :=
  Matrix.normalizedRowRank_mem_Icc A

private theorem rank_zero_one : Matrix.rowRank (0 : Matrix n n K) = 0 ∧
    Matrix.rowRank (1 : Matrix n n K) = Fintype.card n :=
  ⟨Matrix.rowRank_zero, Matrix.rowRank_one⟩

private theorem normalized_product [Nonempty n] (A B : Matrix n n K) :
    Matrix.normalizedRowRank (A * B) ≤ Matrix.normalizedRowRank A ∧
      Matrix.normalizedRowRank (A * B) ≤ Matrix.normalizedRowRank B :=
  ⟨Matrix.normalizedRowRank_mul_le_left A B, Matrix.normalizedRowRank_mul_le_right A B⟩

private theorem normalized_blocks [Nonempty n] [Nonempty o] (A : Matrix n n K) :
    Matrix.normalizedRowRank (Matrix.repeatBlock (o := o) A) =
      Matrix.normalizedRowRank A :=
  Matrix.normalizedRowRank_repeatBlock A

private theorem normalized_reindex (e : n ≃ o) (A : Matrix n n K) :
    Matrix.normalizedRowRank (A.reindex e e) = Matrix.normalizedRowRank A :=
  Matrix.normalizedRowRank_reindex e A

private theorem realize_normalized_rank (k : ℕ) (hk : k ≤ Fintype.card n) :
    ∃ A : Matrix n n K, Matrix.normalizedRowRank A = (k : ℝ) / Fintype.card n :=
  Matrix.exists_normalizedRowRank_eq k hk

omit [Fintype n] [DecidableEq n] in
private theorem opposite_rank (A : Matrix m n Kᵐᵒᵖ) :
    Matrix.rowRank A = 0 ↔ A = 0 :=
  Matrix.rowRank_eq_zero_iff A

omit [Fintype n] [DecidableEq n] in
private theorem empty_rows (A : Matrix (Fin 0) n K) : Matrix.rowRank A = 0 := by
  have hA : A = 0 := Subsingleton.elim _ _
  simp [hA]

private theorem empty_columns (A : Matrix m (Fin 0) K) : Matrix.rowRank A = 0 := by
  have hA : A = 0 := Subsingleton.elim _ _
  simp [hA]

omit [Fintype n] [DecidableEq n] in
private theorem empty_blocks (A : Matrix m n K) :
    Matrix.rowRank (Matrix.repeatBlock (o := Fin 0) A) = 0 := by
  rw [Matrix.rowRank_repeatBlock]
  simp

private theorem empty_normalization :
    Matrix.normalizedRowRank (1 : Matrix (Fin 0) (Fin 0) K) = 0 := by
  simp [Matrix.normalizedRowRank]

end DivisionRings

section RepeatedBlocks

variable {T : Type u} [NonAssocSemiring T]
variable {m : Type v} {o : Type w}
variable [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o]

private theorem block_hom_apply (A : Matrix m m T) :
    Matrix.repeatBlockHom (o := o) A = Matrix.repeatBlock (o := o) A :=
  Matrix.repeatBlockHom_apply A

private theorem block_kronecker (A : Matrix m m T) :
    Matrix.repeatBlockHom (o := o) A = Matrix.kronecker A (1 : Matrix o o T) :=
  Matrix.repeatBlockHom_apply_eq_kronecker_one A

private theorem block_hom_injective [Nonempty o] :
    Function.Injective (Matrix.repeatBlockHom (R := T) (m := m) (o := o)) :=
  Matrix.repeatBlockHom_injective

private theorem block_hom_mul (A B : Matrix m m T) :
    Matrix.repeatBlockHom (o := o) (A * B) =
      Matrix.repeatBlockHom (o := o) A * Matrix.repeatBlockHom (o := o) B :=
  map_mul _ _ _

end RepeatedBlocks

section CommutativeRings

variable {R : Type u} [CommRing R]

private theorem commutative_regular :
    Bass.IsVonNeumannRegular R ↔ IsReduced R ∧ Ring.KrullDimLE 0 R :=
  Bass.isVonNeumannRegular_iff_isReduced_and_krullDimLE_zero

private theorem arbitrary_flat (h : Bass.IsVonNeumannRegular R)
    (M : Type v) [AddCommGroup M] [Module R M] : Module.Flat R M :=
  h.flat M

private theorem zero_dimensional_condition [Ring.KrullDimLE 0 R] :
    Bass.StableRangeCondition R 1 :=
  Bass.stableRangeCondition_one_of_krullDimLE_zero

private theorem zero_dimensional_least [Ring.KrullDimLE 0 R] [Nontrivial R] :
    Bass.IsStableRange R 1 :=
  Bass.stableRange_one_of_krullDimLE_zero

private theorem noetherian_bound (d : ℕ) [IsNoetherianRing R] [Ring.KrullDimLE d R] :
    Bass.StableRangeCondition R (d + 1) :=
  Bass.stableRangeCondition_succ_of_krullDimLE

private theorem dimension_zero_specialization [IsNoetherianRing R] [Ring.KrullDimLE 0 R] :
    Bass.StableRangeCondition R 1 :=
  Bass.stableRangeCondition_succ_of_krullDimLE (d := 0)

private theorem prefix_step (a : ℕ → R) (k : ℕ) :
    Bass.prefixIdeal a (k + 1) = Bass.prefixIdeal a k ⊔ Ideal.span {a k} :=
  Bass.prefixIdeal_succ a k

private theorem prime_avoidance {n : ℕ} (ps : Finset (Ideal R))
    (hp : ∀ P ∈ ps, P.IsPrime)
    (ha : ∀ P ∈ ps, ∀ Q ∈ ps, P ≠ Q → ¬ P ≤ Q)
    (a : R) (r : Fin n → R) (h : ∀ P ∈ ps, a ∉ P ∨ ∃ i, r i ∉ P) :
    ∃ y ∈ Ideal.span (Set.range r), ∀ P ∈ ps, a + y ∉ P :=
  Bass.exists_mem_span_add_avoids_finite_antichain ps hp ha a r h

private theorem row_surjective (n : ℕ) (a : Fin n → R) :
    Bass.IsRightUnimodular a ↔ Function.Surjective (Bass.coefficientRowLinearMap R n a) :=
  Bass.isRightUnimodular_iff_surjective_coefficientRowLinearMap R n a

private theorem scalar_row_apply (n : ℕ) (a x : Fin n → R) :
    Bass.coefficientRowScalarMap R n a x = dotProduct a x :=
  Bass.coefficientRowScalarMap_apply R n a x

private theorem row_split (n : ℕ) (a : Fin n → R) (ha : Bass.IsRightUnimodular a) :
    Nonempty ((LinearMap.ker (Bass.coefficientRowScalarMap R n a) × R) ≃ₗ[R]
      (Fin n → R)) :=
  ⟨Bass.kernelProdEquivOfIsRightUnimodular R n a ha⟩

private theorem fixed_length_kernel (n : ℕ) (hs : Bass.StableRangeCondition R n)
    (a : Fin (n + 1) → R) (ha : Bass.IsRightUnimodular a) :
    Nonempty (LinearMap.ker (Bass.coefficientRowLinearMap R (n + 1) a) ≃ₗ[R]
      (Fin n → R)) :=
  ⟨Bass.coefficientRowKernelEquivSuccOfStableRangeCondition R n hs a ha⟩

private theorem long_kernel (s n : ℕ) (hs : Bass.StableRangeCondition R s)
    (a : Fin n → R) (ha : Bass.IsRightUnimodular a) (hn : s + 1 ≤ n) :
    Module.Free R (LinearMap.ker (Bass.coefficientRowLinearMap R n a)) :=
  Bass.free_ker_coefficientRowLinearMap_of_stableRangeCondition R s n hs a ha hn

private theorem matrix_inverse_kernel (n : ℕ) (i : Fin n) (a : Fin n → R)
    (A B : Matrix (Fin n) (Fin n) R) (hr : A i = a) (hAB : A * B = 1) (hBA : B * A = 1) :
    Nonempty (LinearMap.ker (Bass.coefficientRowLinearMap R n a) ≃ₗ[R]
      ({j : Fin n // j ≠ i} → R)) :=
  ⟨Bass.coefficientRowKernelEquivOfMatrixInverse R n i a A B hr hAB hBA⟩

end CommutativeRings

private theorem nonreduced_condition : Bass.StableRangeCondition (ZMod 4) 1 :=
  Bass.stableRangeCondition_one_of_krullDimLE_zero

private theorem nonzero_square_zero_fixture : ∃ x : ZMod 4, x ≠ 0 ∧ x * x = 0 :=
  ⟨2, by decide, by decide⟩

private theorem trivial_empty_tail :
    Module.Free (ZMod 1)
      (LinearMap.ker (Bass.coefficientRowConsMap (ZMod 1) 0 1 (fun i ↦ Fin.elim0 i))) := by
  apply Bass.free_ker_coefficientRowConsMap_of_stableRangeCondition
    (ZMod 1) 0 zero_ring_condition
  exact ⟨1, fun i ↦ Fin.elim0 i, Subsingleton.elim _ _⟩

section Cancellation

variable {R : Type u} [Ring R]
variable {M : Type v} {A : Type w} {B : Type x}
variable [AddCommGroup M] [AddCommGroup A] [AddCommGroup B]
variable [Module R M] [Module R A] [Module R B]

private theorem cancel_product (h : Bass.StableRangeCondition (Module.End R M) 1)
    (e : (M × A) ≃ₗ[R] (M × B)) : Nonempty (A ≃ₗ[R] B) :=
  Bass.exists_linearEquiv_of_prod_of_end_stableRangeCondition_one h e

private theorem kernel_transport (f : A →ₗ[R] M) (g : B →ₗ[R] M) (e : A ≃ₗ[R] B)
    (h : ∀ x, g (e x) = f x) : Nonempty (LinearMap.ker f ≃ₗ[R] LinearMap.ker g) :=
  ⟨Bass.kernelEquivOfLinearEquiv f g e h⟩

private theorem split_right_inverse (f : A →ₗ[R] B) (g : B →ₗ[R] A)
    (h : f.comp g = LinearMap.id) : Nonempty ((LinearMap.ker f × B) ≃ₗ[R] A) :=
  ⟨Bass.kernelProdEquivOfRightInverse f g h⟩

private theorem zero_power (h : Bass.StableRangeCondition (Module.End R M) 1)
    (e : (Fin 0 → M) ≃ₗ[R] ((Fin 0 → M) × A)) : Subsingleton A :=
  Bass.subsingleton_of_pi_linearEquiv_pi_prod h 0 e

private theorem regular_right_module {P : Type y} [AddCommGroup P] [Module Rᵐᵒᵖ P]
    (h : Bass.IsUnitRegular R) (n : ℕ)
    (e : (Fin n → R) ≃ₗ[Rᵐᵒᵖ] ((Fin n → R) × P)) : Subsingleton P :=
  h.subsingleton_of_fin_linearEquiv_fin_prod n e

end Cancellation

end StableRangePublicAPIClient
