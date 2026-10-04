/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.ElementaryGeneration
public import GeneralLinearGroups.LocalElementaryGeneration

/-!
# Elementary generation and stable determinants under stable range one

Over a commutative ring satisfying Bass's stable-range-one condition, the
elementary subgroup at every finite rank is the determinant-one subgroup.
Consequently the stable elementary subgroup is the kernel of the existing
stable determinant, and its quotient is equivalent to the coefficient units.
The equivalence uses the existing quotient determinant and rank-one section.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter I, §1 (stable-range background and elementary matrices).
* `general-linear-groups`, `LocalElementaryGeneration`,
  `StableDeterminant` and `UnitPivotInduction` (the existing local result,
  quotient determinant, rank-one section and pivot induction generalized here).
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v w

variable {R : Type u} [CommRing R]

private theorem mem_elementarySubgroup_iff_det_eq_one_fin_of_stableRangeCondition_one
    (stable : Bass.StableRangeCondition R 1) {rank : ℕ}
    (matrix : GL (Fin rank) R) :
    matrix ∈ elementarySubgroup (Fin rank) R ↔ det matrix = 1 := by
  constructor
  · intro hmatrix
    exact Matrix.det_elementarySubgroup_eq_one ⟨matrix, hmatrix⟩
  · intro hdet
    obtain ⟨left, right, diagonal, hfactor⟩ :=
      exists_elementary_diagonalization_finite_of_stableRangeCondition_one stable matrix
    have hmatrix := congrArg
      (fun x : GL (Fin rank) R => (x : Matrix (Fin rank) (Fin rank) R)) hfactor
    have hproduct : (∏ index, diagonal index) = 1 := by
      apply Units.ext
      have hfactorDet := Matrix.det_eq_prod_of_elementary_diagonalization
        (L := left) (Q := right) (M := (matrix : Matrix (Fin rank) (Fin rank) R))
        (by simpa only [Units.val_mul, diagonalUnit_val] using hmatrix)
      change (Units.coeHom R) (∏ index, diagonal index) = 1
      rw [map_prod]
      exact hfactorDet.symm.trans (congrArg Units.val hdet)
    have hdiagonal : diagonalUnit diagonal ∈ elementarySubgroup (Fin rank) R :=
      diagonalUnit_mem_elementarySubgroup rank diagonal hproduct
    have hmatrix' : matrix = (left : GL (Fin rank) R)⁻¹ * diagonalUnit diagonal *
        (right : GL (Fin rank) R)⁻¹ := by
      calc
        matrix = ((left : GL (Fin rank) R)⁻¹ *
            ((left : GL (Fin rank) R) * matrix * (right : GL (Fin rank) R))) *
              (right : GL (Fin rank) R)⁻¹ := by group
        _ = (left : GL (Fin rank) R)⁻¹ * diagonalUnit diagonal *
            (right : GL (Fin rank) R)⁻¹ := by rw [hfactor]
    rw [hmatrix']
    exact (elementarySubgroup (Fin rank) R).mul_mem
      ((elementarySubgroup (Fin rank) R).mul_mem
        ((elementarySubgroup (Fin rank) R).inv_mem left.property) hdiagonal)
      ((elementarySubgroup (Fin rank) R).inv_mem right.property)

/-- Over a commutative ring satisfying Bass's `(S₁)`, an invertible matrix
is elementary exactly when its determinant is one, at any finite rank.
This generalizes the local result formalized in `general-linear-groups`'
`LocalElementaryGeneration`. -/
theorem mem_elementarySubgroup_iff_det_eq_one_of_stableRangeCondition_one
    (stable : Bass.StableRangeCondition R 1) {indices : Type v}
    [Fintype indices] [DecidableEq indices] (matrix : GL indices R) :
    matrix ∈ elementarySubgroup indices R ↔ det matrix = 1 := by
  constructor
  · intro hmatrix
    exact Matrix.det_elementarySubgroup_eq_one ⟨matrix, hmatrix⟩
  · intro hdet
    let equiv : indices ≃ Fin (Fintype.card indices) := Fintype.equivOfCardEq (by simp)
    let reindexed : GL (Fin (Fintype.card indices)) R := reindexEquiv R equiv matrix
    have hdet' : det reindexed = det matrix := by
      apply Units.ext
      change (Matrix.reindex equiv equiv (matrix : Matrix indices indices R)).det =
        (matrix : Matrix indices indices R).det
      exact Matrix.det_reindex_self equiv _
    have hreindexed : reindexed ∈ elementarySubgroup (Fin (Fintype.card indices)) R :=
      (mem_elementarySubgroup_iff_det_eq_one_fin_of_stableRangeCondition_one
        stable reindexed).2 (hdet'.trans hdet)
    have hback := reindexEquiv_mem_elementarySubgroup equiv.symm hreindexed
    simpa only [reindexed, ← reindexEquiv_symm, MulEquiv.symm_apply_apply] using hback

namespace StableGL

/-- Under Bass's `(S₁)`, the stable elementary subgroup is precisely the
kernel of the stable determinant formalized in `general-linear-groups`'
`StableDeterminant`; compare its `LocalElementaryGeneration` local case. -/
theorem elementary_eq_ker_det_of_stableRangeCondition_one
    (stable : Bass.StableRangeCondition R 1) :
    stableElementarySubgroup R = (det R).ker := by
  apply le_antisymm (elementary_le_ker_det R)
  intro matrix hmatrix
  obtain ⟨rank, representative, rfl⟩ := exists_stage R matrix
  have hdet : Matrix.GeneralLinearGroup.det representative = 1 := by
    simpa only [MonoidHom.mem_ker, det_stage] using hmatrix
  exact elementary_stage_le R rank
    (Subgroup.mem_map_of_mem _
      ((mem_elementarySubgroup_iff_det_eq_one_of_stableRangeCondition_one
        stable representative).2 hdet))

/-- Under Bass's `(S₁)`, the determinant on the stable elementary quotient
has trivial kernel. -/
theorem quotientDet_ker_eq_bot_of_stableRangeCondition_one
    (stable : Bass.StableRangeCondition R 1) :
    (quotientDet R).ker = ⊥ := by
  apply eq_bot_iff.mpr
  intro quotient hquotient
  obtain ⟨matrix, rfl⟩ :=
    QuotientGroup.mk'_surjective (stableElementarySubgroup R) quotient
  apply (QuotientGroup.eq_one_iff matrix).mpr
  rw [elementary_eq_ker_det_of_stableRangeCondition_one stable]
  apply MonoidHom.mem_ker.mpr
  exact MonoidHom.mem_ker.mp hquotient

/-- The existing quotient determinant is injective under Bass's `(S₁)`. -/
theorem quotientDet_injective_of_stableRangeCondition_one
    (stable : Bass.StableRangeCondition R 1) :
    Function.Injective (quotientDet R) :=
  (quotientDet R).ker_eq_bot_iff.mp
    (quotientDet_ker_eq_bot_of_stableRangeCondition_one stable)

/-- The determinant identifies the stable elementary quotient with the
coefficient units under Bass's `(S₁)`. Its inverse is the rank-one section
formalized in `general-linear-groups`' `StableDeterminant`; this generalizes
the local equivalence in `LocalElementaryGeneration`. -/
noncomputable def quotientDetMulEquivOfStableRangeConditionOne
    (stable : Bass.StableRangeCondition R 1) :
    (StableGL R ⧸ stableElementarySubgroup R) ≃* Rˣ where
  toFun := quotientDet R
  invFun := quotientRankOneUnits R
  left_inv := by
    intro quotient
    apply quotientDet_injective_of_stableRangeCondition_one stable
    exact quotientDet_quotientRankOneUnits R (quotientDet R quotient)
  right_inv := quotientDet_quotientRankOneUnits R
  map_mul' := (quotientDet R).map_mul

/-- The equivalence evaluates as the existing quotient determinant. -/
@[simp]
theorem quotientDetMulEquivOfStableRangeConditionOne_apply
    (stable : Bass.StableRangeCondition R 1)
    (quotient : StableGL R ⧸ stableElementarySubgroup R) :
    quotientDetMulEquivOfStableRangeConditionOne stable quotient =
      quotientDet R quotient := rfl

/-- The inverse equivalence evaluates as the existing rank-one section. -/
@[simp]
theorem quotientDetMulEquivOfStableRangeConditionOne_symm_apply
    (stable : Bass.StableRangeCondition R 1) (unit : Rˣ) :
    (quotientDetMulEquivOfStableRangeConditionOne stable).symm unit =
      quotientRankOneUnits R unit := rfl

/-- The rank-one section recovers every stable elementary class under `(S₁)`. -/
@[simp]
theorem quotientRankOneUnits_quotientDet_of_stableRangeCondition_one
    (stable : Bass.StableRangeCondition R 1)
    (quotient : StableGL R ⧸ stableElementarySubgroup R) :
    quotientRankOneUnits R (quotientDet R quotient) = quotient := by
  simpa only [quotientDetMulEquivOfStableRangeConditionOne_apply,
    quotientDetMulEquivOfStableRangeConditionOne_symm_apply] using
      (quotientDetMulEquivOfStableRangeConditionOne stable).symm_apply_apply quotient

/-- Two stable elementary classes agree exactly when their determinants do. -/
theorem quotientDet_eq_iff_of_stableRangeCondition_one
    (stable : Bass.StableRangeCondition R 1)
    (first second : StableGL R ⧸ stableElementarySubgroup R) :
    quotientDet R first = quotientDet R second ↔ first = second := by
  constructor
  · intro equality
    exact quotientDet_injective_of_stableRangeCondition_one stable equality
  · intro equality
    rw [equality]

/-- The quotient equivalence commutes with coefficient homomorphisms
between commutative rings satisfying Bass's `(S₁)`. -/
theorem quotientDetMulEquivOfStableRangeConditionOne_map
    {S : Type w} [CommRing S] (stableR : Bass.StableRangeCondition R 1)
    (stableS : Bass.StableRangeCondition S 1) (f : R →+* S)
    (quotient : StableGL R ⧸ stableElementarySubgroup R) :
    quotientDetMulEquivOfStableRangeConditionOne stableS
      (QuotientGroup.map (stableElementarySubgroup R)
        (stableElementarySubgroup S) (map f)
        ((Subgroup.map_le_iff_le_comap).mp (map_elementarySubgroup_le f)) quotient) =
      Units.map f (quotientDetMulEquivOfStableRangeConditionOne stableR quotient) := by
  simpa only [quotientDetMulEquivOfStableRangeConditionOne_apply] using
    quotientDet_map f quotient

/-- The inverse equivalence commutes with coefficient homomorphisms
between commutative rings satisfying Bass's `(S₁)`. -/
theorem quotientDetMulEquivOfStableRangeConditionOne_symm_map
    {S : Type w} [CommRing S] (stableR : Bass.StableRangeCondition R 1)
    (stableS : Bass.StableRangeCondition S 1) (f : R →+* S) (unit : Rˣ) :
    QuotientGroup.map (stableElementarySubgroup R)
        (stableElementarySubgroup S) (map f)
        ((Subgroup.map_le_iff_le_comap).mp (map_elementarySubgroup_le f))
        ((quotientDetMulEquivOfStableRangeConditionOne stableR).symm unit) =
      (quotientDetMulEquivOfStableRangeConditionOne stableS).symm (Units.map f unit) := by
  simpa only [quotientDetMulEquivOfStableRangeConditionOne_symm_apply] using
    quotientRankOneUnits_map f unit

/-- For local rings the stable-range-one equivalence is the existing local
quotient-determinant equivalence. -/
theorem quotientDetMulEquivOfStableRangeConditionOne_eq_local
    [IsLocalRing R] (stable : Bass.StableRangeCondition R 1) :
    quotientDetMulEquivOfStableRangeConditionOne stable = quotientDetMulEquiv R := by
  ext quotient
  rfl

end StableGL

end Matrix.GeneralLinearGroup
