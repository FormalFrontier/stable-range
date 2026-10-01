/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Regular
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod

/-!
# Free-summand cancellation from stable range one

This file proves that a module can be cancelled from a binary product whenever
its endomorphism ring satisfies Bass's right stable-range-one condition.  The
proof is an explicit two-by-two block reduction and imposes no finiteness or
projectivity hypothesis on any module.
-/

set_option warningAsError true

@[expose] public section

namespace Bass

universe u v w x

variable {R : Type u} [Ring R]
variable {M : Type v} {A : Type w} {B : Type x}
variable [AddCommGroup M] [AddCommGroup A] [AddCommGroup B]
variable [Module R M] [Module R A] [Module R B]

/-- A module whose endomorphism ring satisfies `(S₁)` cancels from a binary
product. No finiteness or projectivity assumption is required. -/
theorem exists_linearEquiv_of_prod_of_end_stableRangeCondition_one
    (h : StableRangeCondition (Module.End R M) 1)
    (e : (M × A) ≃ₗ[R] (M × B)) :
    Nonempty (A ≃ₗ[R] B) := by
  let a : Module.End R M :=
    (LinearMap.fst R M B).comp
      (e.toLinearMap.comp (LinearMap.inl R M A))
  let b : A →ₗ[R] M :=
    (LinearMap.fst R M B).comp
      (e.toLinearMap.comp (LinearMap.inr R M A))
  let c : M →ₗ[R] B :=
    (LinearMap.snd R M B).comp
      (e.toLinearMap.comp (LinearMap.inl R M A))
  let d : A →ₗ[R] B :=
    (LinearMap.snd R M B).comp
      (e.toLinearMap.comp (LinearMap.inr R M A))
  let a' : Module.End R M :=
    (LinearMap.fst R M A).comp
      (e.symm.toLinearMap.comp (LinearMap.inl R M B))
  let c' : M →ₗ[R] A :=
    (LinearMap.snd R M A).comp
      (e.symm.toLinearMap.comp (LinearMap.inl R M B))
  have he_apply (m : M) (x : A) :
      e (m, x) = (a m + b x, c m + d x) := by
    rw [show (m, x) = (m, 0) + (0, x) by simp, map_add]
    rfl
  have he_symm_apply (m : M) (y : B) :
      e.symm (m, y) = (a' m +
        ((LinearMap.fst R M A).comp
          (e.symm.toLinearMap.comp (LinearMap.inr R M B))) y,
        c' m +
        ((LinearMap.snd R M A).comp
          (e.symm.toLinearMap.comp (LinearMap.inr R M B))) y) := by
    rw [show (m, y) = (m, 0) + (0, y) by simp, map_add]
    rfl
  let p : Module.End R M := b.comp c'
  have hrow : IsRightUnimodularCons p (fun _ : Fin 1 ↦ a) := by
    refine ⟨1, fun _ ↦ a', ?_⟩
    rw [Fin.sum_univ_one]
    ext m
    change p m + a (a' m) = m
    have hm := congrArg Prod.fst (e.apply_symm_apply (m, 0))
    rw [he_symm_apply] at hm
    simp only [map_zero, add_zero] at hm
    rw [he_apply] at hm
    dsimp only [p, LinearMap.comp_apply]
    rw [add_comm]
    exact hm
  obtain ⟨t, w, hw⟩ := h p (fun _ : Fin 1 ↦ a) hrow
  let u : Module.End R M := a - p * t 0
  have huw : u * w 0 = 1 := by
    simpa only [IsRightUnimodular, Fin.sum_univ_one, u] using hw
  have hwu : w 0 * u = 1 :=
    (stableRangeCondition_one_isDedekindFinite h).mul_eq_one_symm huw
  let q : M →ₗ[R] A := c'.comp (t 0)
  let r : M →ₗ[R] B := c - d.comp q
  let s : A →ₗ[R] B := d - (r.comp (w 0)).comp b
  let T₁ : (M × A) ≃ₗ[R] (M × A) :=
    (LinearEquiv.refl R M).skewProd (LinearEquiv.refl R A) (-q)
  let T₂ : (M × B) ≃ₗ[R] (M × B) :=
    (LinearEquiv.refl R M).skewProd (LinearEquiv.refl R B) (-(r.comp (w 0)))
  let F : (M × A) ≃ₗ[R] (M × B) := T₁.trans (e.trans T₂)
  have huw_apply (m : M) : u (w 0 m) = m := by
    have hm := congrArg (fun f : Module.End R M ↦ f m) huw
    simpa only [Module.End.mul_apply, Module.End.one_apply] using hm
  have hwu_apply (m : M) : w 0 (u m) = m := by
    have hm := congrArg (fun f : Module.End R M ↦ f m) hwu
    simpa only [Module.End.mul_apply, Module.End.one_apply] using hm
  have hu_apply (m : M) : u m = a m - b (q m) := by
    rfl
  have htop (m : M) (x : A) : a m + b (x + -q m) = u m + b x := by
    rw [map_add, map_neg, hu_apply]
    abel
  have hF (m : M) (x : A) : F (m, x) = (u m + b x, s x) := by
    change T₂ (e (T₁ (m, x))) = (u m + b x, s x)
    dsimp only [T₁, LinearEquiv.skewProd_apply, LinearEquiv.refl_apply,
      LinearMap.neg_apply]
    rw [he_apply]
    dsimp only [T₂, LinearEquiv.skewProd_apply, LinearEquiv.refl_apply]
    apply Prod.ext
    · exact htop m x
    · rw [htop, map_add, map_neg]
      simp only [LinearMap.neg_apply, LinearMap.comp_apply]
      simp only [← sub_eq_add_neg]
      calc
        c m + (d x - d (q m)) - r (w 0 (u m + b x)) =
            r m + d x - r (w 0 (u m) + w 0 (b x)) := by
              rw [map_add]
              dsimp only [r, LinearMap.sub_apply, LinearMap.comp_apply]
              abel
        _ = r m + d x - (r m + r (w 0 (b x))) := by
              rw [map_add, hwu_apply]
        _ = d x - r (w 0 (b x)) := by abel
        _ = s x := rfl
  have hs_injective : Function.Injective s := by
    intro x y hxy
    let m : M := -(w 0) (b (x - y))
    have hzero : F (m, x - y) = 0 := by
      rw [hF]
      change (u m + b (x - y), s (x - y)) = (0, 0)
      have hfirst : u m + b (x - y) = 0 := by
        simp only [m, map_neg, huw_apply]
        abel
      have hsecond : s (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      rw [hfirst, hsecond]
    have hpair : (m, x - y) = 0 := F.injective (by simpa using hzero)
    have : x - y = 0 := congrArg Prod.snd hpair
    exact sub_eq_zero.mp (by simpa using this)
  have hs_surjective : Function.Surjective s := by
    intro y
    obtain ⟨mx, hmx⟩ := F.surjective (0, y)
    refine ⟨mx.2, ?_⟩
    rw [hF] at hmx
    exact congrArg Prod.snd hmx
  exact ⟨LinearEquiv.ofBijective s ⟨hs_injective, hs_surjective⟩⟩

/-- If the endomorphism ring of `M` satisfies `(S₁)`, a finite free power of
`M` cannot absorb a nontrivial complementary module. -/
theorem subsingleton_of_pi_linearEquiv_pi_prod
    {P : Type x} [AddCommGroup P] [Module R P]
    (h : StableRangeCondition (Module.End R M) 1) (n : ℕ)
    (e : (Fin n → M) ≃ₗ[R] ((Fin n → M) × P)) :
    Subsingleton P := by
  induction n with
  | zero =>
      constructor
      intro x y
      let z : Fin 0 → M := 0
      have heq : e.symm (z, x) = e.symm (z, y) := Subsingleton.elim _ _
      have hpair : (z, x) = (z, y) := e.symm.injective heq
      exact congrArg Prod.snd hpair
  | succ n ih =>
      let split : (Fin (n + 1) → M) ≃ₗ[R] (M × (Fin n → M)) :=
        LinearEquiv.piCongrLeft R (fun _ ↦ M) (finSuccEquiv n) ≪≫ₗ
          .piOptionEquivProd _
      let reassoc : ((M × (Fin n → M)) × P) ≃ₗ[R]
          (M × ((Fin n → M) × P)) :=
        LinearEquiv.prodAssoc R M (Fin n → M) P
      let transformed : (M × (Fin n → M)) ≃ₗ[R]
          (M × ((Fin n → M) × P)) :=
        split.symm.trans (e.trans ((split.prodCongr (LinearEquiv.refl R P)).trans reassoc))
      obtain ⟨cancelled⟩ :=
        exists_linearEquiv_of_prod_of_end_stableRangeCondition_one h transformed
      exact ih cancelled

/-- A unit-regular ring satisfies the finite-free cancellation condition for
its regular right module. In Lean this right module is a left module over the
opposite ring. -/
theorem IsUnitRegular.subsingleton_of_fin_linearEquiv_fin_prod
    {P : Type x} [AddCommGroup P] [Module Rᵐᵒᵖ P]
    (h : IsUnitRegular R) (n : ℕ)
    (e : (Fin n → R) ≃ₗ[Rᵐᵒᵖ] ((Fin n → R) × P)) :
    Subsingleton P := by
  apply subsingleton_of_pi_linearEquiv_pi_prod _ n e
  exact h.stableRangeCondition_one.map_equiv (RingEquiv.moduleEndSelfOp R)

end Bass
