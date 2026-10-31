/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.RowKernel

/-!
# Split-kernel reconstructions through the row-kernel API

Over a ring, a specified linear section reconstructs a vector from its kernel
component `a - g (f a)` and its image `f a`. Conversely, reconstructing a pair
recovers the same kernel element and image. These examples keep the scalar,
source and target universes independent.

Composing the specified section with the identity does not change the forward
reconstruction or the first inverse coordinate. This compares equal sections,
not arbitrary choices of section.

## References

* Mathlib, `LinearAlgebra.Prod` and `Algebra.Module.Submodule.LinearMap`
  (coproducts, products and codomain restrictions of linear maps).
-/

namespace StableRangeTests.SplitSurjectiveCompatibility

universe uR uA uB

variable {R : Type uR} {A : Type uA} {B : Type uB}
variable [ringR : Ring R] [groupA : AddCommGroup A] [moduleA : Module R A]
  [groupB : AddCommGroup B] [moduleB : Module R B]

-- Test kernel reconstruction through the retained public `_proof_2`–`_proof_5` spellings.
-- Retained constructors and fixed `_proof_2`–`_proof_5` spellings test kernel reconstruction.
set_option linter.deprecated false in
set_option linter.auxLemma false in
private theorem kernel_image_reconstruction
    (f : A →ₗ[R] B) (g : B →ₗ[R] A) (hfg : f.comp g = LinearMap.id)
    (a : A) (p : f.ker × B) :
    ∃ k : A →ₗ[R] f.ker,
      (k a).val = a - g (f a) ∧
      (f.ker.subtype.coprod g) ((k.prod f) a) = a ∧
      (k.prod f) ((f.ker.subtype.coprod g) p) = p ∧
      (Bass.kernelProdEquivOfRightInverse.{uR, uA, uB}
        (R := R) (A := A) (B := B) (f := f) (g := g) (hfg := hfg)).symm a =
          (k.prod f) a := by
  have hpoint (b : B) : f (g b) = b :=
    Bass.kernelProdEquivOfRightInverse._proof_5.{uB, uR, uA}
      (R := R) (A := A) (B := B) (f := f) (g := g) hfg b
  let k : A →ₗ[R] f.ker :=
    LinearMap.codRestrict f.ker (LinearMap.id - g.comp f)
      (fun x ↦ Bass.kernelProdEquivOfRightInverse._proof_2.{uA, uR, uB}
        (R := R) (A := A) (B := B) (f := f) (g := g) hpoint x)
  let φ : (f.ker × B) →ₗ[R] A := f.ker.subtype.coprod g
  let ψ : A →ₗ[R] (f.ker × B) := k.prod f
  have hφψ : φ.comp ψ = LinearMap.id :=
    Bass.kernelProdEquivOfRightInverse._proof_3.{uA, uR, uB}
      (R := R) (A := A) (B := B) (f := f) (g := g) (hfg' := hpoint)
  have hψφ : ψ.comp φ = LinearMap.id :=
    Bass.kernelProdEquivOfRightInverse._proof_4.{uA, uB, uR}
      (R := R) (A := A) (B := B) (f := f) (g := g) (hfg' := hpoint)
  have hconstructor :
      Bass.kernelProdEquivOfRightInverse.{uR, uA, uB}
          (R := R) (A := A) (B := B) (f := f) (g := g) (hfg := hfg) =
        LinearEquiv.ofLinearMap φ ψ hφψ hψφ :=
    @Bass.kernelProdEquivOfRightInverse.eq_1.{uR, uA, uB}
      R A B ringR groupA moduleA groupB moduleB f g hfg
  refine ⟨k, rfl, ?_, ?_, ?_⟩
  · exact LinearMap.congr_fun hφψ a
  · exact LinearMap.congr_fun hψφ p
  · rw [hconstructor]
    rfl

-- Test explicit kernel reconstruction through retained public `_proof_2`–`_proof_5` spellings.
-- Explicit dictionaries test the retained constructor and fixed `_proof_2`–`_proof_5` API.
set_option linter.deprecated false in
set_option linter.auxLemma false in
private theorem kernel_image_reconstruction_explicit
    (f : A →ₗ[R] B) (g : B →ₗ[R] A) (hfg : f.comp g = LinearMap.id)
    (a : A) (p : f.ker × B) :
    ∃ k : A →ₗ[R] f.ker,
      (k a).val = a - g (f a) ∧
      (f.ker.subtype.coprod g) ((k.prod f) a) = a ∧
      (k.prod f) ((f.ker.subtype.coprod g) p) = p ∧
      (@Bass.kernelProdEquivOfRightInverse.{uR, uA, uB}
        R A B ringR groupA moduleA groupB moduleB f g hfg).symm a =
          (k.prod f) a := by
  have hpoint (b : B) : f (g b) = b :=
    @Bass.kernelProdEquivOfRightInverse._proof_5.{uB, uR, uA}
      R A B ringR groupA moduleA groupB moduleB f g hfg b
  let k : A →ₗ[R] f.ker :=
    LinearMap.codRestrict f.ker (LinearMap.id - g.comp f)
      (fun x ↦ @Bass.kernelProdEquivOfRightInverse._proof_2.{uA, uR, uB}
        R A B ringR groupA moduleA groupB moduleB f g hpoint x)
  let φ : (f.ker × B) →ₗ[R] A := f.ker.subtype.coprod g
  let ψ : A →ₗ[R] (f.ker × B) := k.prod f
  have hφψ : φ.comp ψ = LinearMap.id :=
    @Bass.kernelProdEquivOfRightInverse._proof_3.{uA, uR, uB}
      R A B ringR groupA moduleA groupB moduleB f g hpoint
  have hψφ : ψ.comp φ = LinearMap.id :=
    @Bass.kernelProdEquivOfRightInverse._proof_4.{uA, uB, uR}
      R A B ringR groupA moduleA groupB moduleB f g hpoint
  have hconstructor :
      @Bass.kernelProdEquivOfRightInverse.{uR, uA, uB}
          R A B ringR groupA moduleA groupB moduleB f g hfg =
        LinearEquiv.ofLinearMap φ ψ hφψ hψφ :=
    @Bass.kernelProdEquivOfRightInverse.eq_def.{uR, uA, uB}
      R A B ringR groupA moduleA groupB moduleB f g hfg
  refine ⟨k, rfl, ?_, ?_, ?_⟩
  · exact LinearMap.congr_fun hφψ a
  · exact LinearMap.congr_fun hψφ p
  · rw [hconstructor]
    rfl

-- Identity-composed sections compare retained and modern reconstruction coordinates.
set_option linter.deprecated false in
private theorem identity_composite_section_coordinates
    (f : A →ₗ[R] B) (g : B →ₗ[R] A) (hfg : f.comp g = LinearMap.id)
    (p : f.ker × B) (a : A) :
    Bass.kernelProdEquivOfRightInverse.{uR, uA, uB}
        (R := R) (A := A) (B := B) (f := f)
        (g := (LinearMap.id : A →ₗ[R] A).comp g)
        (hfg := by simpa only [LinearMap.id_comp] using hfg) p = p.1.val + g p.2 ∧
      ((Bass.kernelProdEquivOfRightInverse.{uR, uA, uB}
        (R := R) (A := A) (B := B) (f := f)
        (g := (LinearMap.id : A →ₗ[R] A).comp g)
        (hfg := by simpa only [LinearMap.id_comp] using hfg)).symm a).1.val =
          a - g (f a) := by
  have hsame :
      Bass.kernelProdEquivOfRightInverse.{uR, uA, uB}
          (R := R) (A := A) (B := B) (f := f) (g := g) (hfg := hfg) =
        Bass.kernelProdEquivOfRightInverse.{uR, uA, uB}
          (R := R) (A := A) (B := B) (f := f)
          (g := (LinearMap.id : A →ₗ[R] A).comp g)
          (hfg := by simpa only [LinearMap.id_comp] using hfg) :=
    rfl
  constructor
  · rw [← hsame]
    exact LinearMap.kerProdEquivOfRightInverse_apply f g hfg p
  · rw [← hsame]
    exact LinearMap.kerProdEquivOfRightInverse_symm_fst f g hfg a

-- Explicit dictionaries compare retained and modern coordinates for identity-composed sections.
set_option linter.deprecated false in
private theorem identity_composite_section_coordinates_explicit
    (f : A →ₗ[R] B) (g : B →ₗ[R] A) (hfg : f.comp g = LinearMap.id)
    (p : f.ker × B) (a : A) :
    (@Bass.kernelProdEquivOfRightInverse.{uR, uA, uB}
      R A B ringR groupA moduleA groupB moduleB f
      ((LinearMap.id : A →ₗ[R] A).comp g)
      (by simpa only [LinearMap.id_comp] using hfg)) p = p.1.val + g p.2 ∧
      ((@Bass.kernelProdEquivOfRightInverse.{uR, uA, uB}
        R A B ringR groupA moduleA groupB moduleB f
        ((LinearMap.id : A →ₗ[R] A).comp g)
        (by simpa only [LinearMap.id_comp] using hfg)).symm a).1.val =
          a - g (f a) := by
  have hsame :
      @Bass.kernelProdEquivOfRightInverse.{uR, uA, uB}
          R A B ringR groupA moduleA groupB moduleB f g hfg =
        @Bass.kernelProdEquivOfRightInverse.{uR, uA, uB}
          R A B ringR groupA moduleA groupB moduleB f
          ((LinearMap.id : A →ₗ[R] A).comp g)
          (by simpa only [LinearMap.id_comp] using hfg) :=
    rfl
  constructor
  · rw [← hsame]
    exact LinearMap.kerProdEquivOfRightInverse_apply f g hfg p
  · rw [← hsame]
    exact LinearMap.kerProdEquivOfRightInverse_symm_fst f g hfg a

end StableRangeTests.SplitSurjectiveCompatibility
