# Historical generated API reference

This is a **frozen historical doc-gen4 display**, not today's API index. It
records 121 named sites across twelve mathematical leaves at the original
source revision bound by the [manifest](api-manifest.json). The aggregate root
and original private regression client had no native public display sites;
that client had 65 named private tests outside this display selection. Today's
relocated client also has a public zero-ring fixture, not a production result.
The sites are not a raw/private/generated declaration census or proof audit.

The headers below preserve the original native *display* signatures, including
implicit parameters and visible modifiers, not proof bodies or necessarily
current binders. In particular `Matrix.rowRank_mul_le_left` below shows an
obsolete explicit `DecidableEq n` parameter absent from today's declaration.
The [Source] links navigate to files in this checkout, but their line ranges
belong to the **original snapshot** and may be stale in current files. Consult
the current Lean modules for current signatures and positions; for historical
source ranges use the manifest's original source revision. Native
pretty-printing can also suppress inferable types.
[Generation and limits](README.md) · [Credits](CREDITS.md) ·
[source and tool manifest](api-manifest.json).

Missing source docstrings are labeled as separately authored API notes.

## StableRange.Basic

Scope: mathematical library leaf.

### Bass.IsRightUnimodular

```lean
def Bass.IsRightUnimodular {R : Type u} [Ring R] {n : ℕ} (r : Fin n → R) : Prop
```

A finite row is right-unimodular when its entries generate `1` by a right
linear combination.

[Source](../StableRange/Basic.lean#L30-L33) (native database range lines 30–33).

### Bass.IsRightUnimodularCons

```lean
def Bass.IsRightUnimodularCons {R : Type u} [Ring R] {n : ℕ} (r0 : R) (r : Fin n → R) : Prop
```

Right-unimodularity with a distinguished first entry separated from the
remaining finite row.

[Source](../StableRange/Basic.lean#L35-L39) (native database range lines 35–39).

### Bass.isRightUnimodular_finSucc_iff

```lean
theorem Bass.isRightUnimodular_finSucc_iff {R : Type u} [Ring R] {n : ℕ} (r : Fin (n + 1) → R) : IsRightUnimodular r ↔ IsRightUnimodularCons (r 0) fun (i : Fin n) => r i.succ
```

Separating the first coordinate preserves right-unimodularity.

[Source](../StableRange/Basic.lean#L41-L52) (native database range lines 41–52).

### Bass.StableRangeCondition

```lean
def Bass.StableRangeCondition (R : Type u) [Ring R] (n : ℕ) : Prop
```

Bass's condition `(S_n)`, stated with the distinguished first coordinate
separated from a row of length `n`.

[Source](../StableRange/Basic.lean#L54-L58) (native database range lines 54–58).

### Bass.stableRangeCondition_iff_literal

```lean
theorem Bass.stableRangeCondition_iff_literal {R : Type u} [Ring R] (n : ℕ) : StableRangeCondition R n ↔ ∀ (r : Fin (n + 1) → R), IsRightUnimodular r → ∃ (t : Fin n → R), IsRightUnimodular fun (i : Fin n) => r i.succ - r 0 * t i
```

The separated form of `(S_n)` is equivalent to its literal formulation on
a right-unimodular row of length `n + 1`.

[Source](../StableRange/Basic.lean#L60-L76) (native database range lines 60–76).

### Bass.IsRightUnimodular.map

```lean
theorem Bass.IsRightUnimodular.map {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) {n : ℕ} {r : Fin n → R} (hr : IsRightUnimodular r) : IsRightUnimodular fun (i : Fin n) => f (r i)
```

A ring homomorphism preserves right-unimodularity.

[Source](../StableRange/Basic.lean#L78-L84) (native database range lines 78–84).

### Bass.IsRightUnimodularCons.map

```lean
theorem Bass.IsRightUnimodularCons.map {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) {n : ℕ} {r0 : R} {r : Fin n → R} (hr : IsRightUnimodularCons r0 r) : IsRightUnimodularCons (f r0) fun (i : Fin n) => f (r i)
```

A ring homomorphism preserves the separated form of
right-unimodularity.

[Source](../StableRange/Basic.lean#L86-L95) (native database range lines 86–95).

### Bass.StableRangeCondition.map_equiv

```lean
theorem Bass.StableRangeCondition.map_equiv {R : Type u} {S : Type v} [Ring R] [Ring S] {n : ℕ} (h : StableRangeCondition R n) (e : R ≃+* S) : StableRangeCondition S n
```

Bass's stable-range condition is preserved by a ring equivalence.

[Source](../StableRange/Basic.lean#L97-L106) (native database range lines 97–106).

### Bass.stableRangeCondition_equiv_iff

```lean
theorem Bass.stableRangeCondition_equiv_iff {R : Type u} {S : Type v} [Ring R] [Ring S] (e : R ≃+* S) (n : ℕ) : StableRangeCondition R n ↔ StableRangeCondition S n
```

Bass's stable-range condition is invariant under ring equivalence.

[Source](../StableRange/Basic.lean#L108-L113) (native database range lines 108–113).

### Bass.stableRangeCondition_succ

```lean
theorem Bass.stableRangeCondition_succ {R : Type u} [Ring R] (n : ℕ) : StableRangeCondition R n → StableRangeCondition R (n + 1)
```

Vaserstein's one-step implication: `(S_n)` implies `(S_(n+1))`.

[Source](../StableRange/Basic.lean#L115-L140) (native database range lines 115–140).

### Bass.stableRangeCondition_mono

```lean
theorem Bass.stableRangeCondition_mono {R : Type u} [Ring R] {m n : ℕ} (hmn : m ≤ n) : StableRangeCondition R m → StableRangeCondition R n
```

The stable-range conditions are monotone in their index.

[Source](../StableRange/Basic.lean#L142-L148) (native database range lines 142–148).

### Bass.IsStableRange

```lean
def Bass.IsStableRange (R : Type u) [Ring R] (s : ℕ) : Prop
```

`s` is the least natural index satisfying Bass's stable-range condition.

This relational formulation does not assign a default natural number to a ring
for which no finite stable range has been supplied.

[Source](../StableRange/Basic.lean#L150-L155) (native database range lines 150–155).

### Bass.stableRangeCondition_of_isStableRange

```lean
theorem Bass.stableRangeCondition_of_isStableRange {R : Type u} [Ring R] {s n : ℕ} (hs : IsStableRange R s) (hsn : s ≤ n) : StableRangeCondition R n
```

Every condition whose index is at least a supplied least stable range
holds.

[Source](../StableRange/Basic.lean#L157-L162) (native database range lines 157–162).

## StableRange.Quotient

Scope: mathematical library leaf.

### Bass.exists_rightUnimodular_lift_of_surjective

```lean
theorem Bass.exists_rightUnimodular_lift_of_surjective {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) (hf : Function.Surjective ⇑f) {m : ℕ} (hm : StableRangeCondition R m) (q : Fin m → S) (hq : IsRightUnimodular q) : ∃ (r : Fin m → R), (∀ (i : Fin m), f (r i) = q i) ∧ IsRightUnimodular r
```

If `(S_m)` holds in the domain, every right-unimodular row of length `m`
over the codomain of a surjective ring homomorphism has a right-unimodular
lift.

[Source](../StableRange/Quotient.lean#L28-L51) (native database range lines 28–51).

### Bass.stableRangeCondition_of_surjective

```lean
theorem Bass.stableRangeCondition_of_surjective {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) (hf : Function.Surjective ⇑f) {n : ℕ} (hn : StableRangeCondition R n) : StableRangeCondition S n
```

Every Bass stable-range condition descends along a surjective ring
homomorphism.

[Source](../StableRange/Quotient.lean#L53-L71) (native database range lines 53–71).

### Bass.stableRangeCondition_quotient

```lean
theorem Bass.stableRangeCondition_quotient {R : Type u} [Ring R] (I : TwoSidedIdeal R) {n : ℕ} (hn : StableRangeCondition R n) : StableRangeCondition (R ⧸ TwoSidedIdeal.asIdeal I) n
```

Every Bass stable-range condition descends to a two-sided quotient.

[Source](../StableRange/Quotient.lean#L73-L79) (native database range lines 73–79).

### Bass.stableRange_quotient_le

```lean
theorem Bass.stableRange_quotient_le {R : Type u} [Ring R] (I : TwoSidedIdeal R) {sR sQ : ℕ} (hR : IsStableRange R sR) (hQ : IsStableRange (R ⧸ TwoSidedIdeal.asIdeal I) sQ) : sQ ≤ sR
```

The least stable range of a two-sided quotient is at most that of the
original ring, conditional on supplied least indices.

[Source](../StableRange/Quotient.lean#L81-L87) (native database range lines 81–87).

### Bass.isRightUnimodular_of_quotient

```lean
theorem Bass.isRightUnimodular_of_quotient {R : Type u} [Ring R] (I : TwoSidedIdeal R) (hI : I.IsQuasiregular) {n : ℕ} (r : Fin n → R) (hr : IsRightUnimodular fun (i : Fin n) => (Ideal.Quotient.mk (TwoSidedIdeal.asIdeal I)) (r i)) : IsRightUnimodular r
```

A row whose image in a quotient by a quasi-regular two-sided ideal is
right-unimodular is already right-unimodular.

After lifting a quotient witness, its scalar product with the row differs from
`1` by an element of the ideal and is therefore a unit. Multiplying all
witnesses on the right by its inverse normalizes the product to `1`.

[Source](../StableRange/Quotient.lean#L89-L123) (native database range lines 89–123).

### Bass.stableRangeCondition_quotient_iff

```lean
theorem Bass.stableRangeCondition_quotient_iff {R : Type u} [Ring R] (I : TwoSidedIdeal R) (hI : I.IsQuasiregular) (n : ℕ) : StableRangeCondition R n ↔ StableRangeCondition (R ⧸ TwoSidedIdeal.asIdeal I) n
```

A quasi-regular quotient satisfies exactly the same Bass stable-range
conditions as the original ring.

[Source](../StableRange/Quotient.lean#L125-L142) (native database range lines 125–142).

### Bass.stableRange_eq_quotient

```lean
theorem Bass.stableRange_eq_quotient {R : Type u} [Ring R] (I : TwoSidedIdeal R) (hI : I.IsQuasiregular) {sR sQ : ℕ} (hR : IsStableRange R sR) (hQ : IsStableRange (R ⧸ TwoSidedIdeal.asIdeal I) sQ) : sR = sQ
```

Quotienting by a quasi-regular two-sided ideal preserves supplied least
stable-range indices.

[Source](../StableRange/Quotient.lean#L144-L153) (native database range lines 144–153).

## StableRange.Local

Scope: mathematical library leaf.

### Bass.isUnit_of_mul_eq_one_right

```lean
theorem Bass.isUnit_of_mul_eq_one_right {R : Type u} [Ring R] [IsLocalRing R] {a b : R} (hab : a * b = 1) : IsUnit a
```

In a noncommutative local ring, an element with a right inverse is a unit.

The proof does not assume direct finiteness. It applies locality to the
idempotent `b * a`; if `1 - b * a` were a unit, then its product with `b`
would force `b = 0`, contradicting `a * b = 1`.

[Source](../StableRange/Local.lean#L29-L57) (native database range lines 29–57).

### Bass.isUnit_first_or_isUnit_second

```lean
theorem Bass.isUnit_first_or_isUnit_second {R : Type u} [Ring R] [IsLocalRing R] (r0 : R) (r : Fin 1 → R) (hr : IsRightUnimodularCons r0 r) : IsUnit r0 ∨ IsUnit (r 0)
```

In a local ring, one entry of a right-unimodular pair is a unit.

[Source](../StableRange/Local.lean#L59-L85) (native database range lines 59–85).

### Bass.stableRangeCondition_one_of_isLocalRing

```lean
theorem Bass.stableRangeCondition_one_of_isLocalRing {R : Type u} [Ring R] [IsLocalRing R] : StableRangeCondition R 1
```

Every local ring satisfies Bass's condition `(S_1)`.

[Source](../StableRange/Local.lean#L87-L107) (native database range lines 87–107).

### Bass.not_stableRangeCondition_zero

```lean
theorem Bass.not_stableRangeCondition_zero {R : Type u} [Ring R] [Nontrivial R] : ¬StableRangeCondition R 0
```

In a nontrivial ring, Bass's condition `(S_0)` is impossible.

[Source](../StableRange/Local.lean#L109-L120) (native database range lines 109–120).

### Bass.stableRange_one_of_isLocalRing

```lean
theorem Bass.stableRange_one_of_isLocalRing {R : Type u} [Ring R] [IsLocalRing R] : IsStableRange R 1
```

Every local ring has least Bass stable range one.

[Source](../StableRange/Local.lean#L122-L129) (native database range lines 122–129).

## StableRange.Regular

Scope: mathematical library leaf.

### Bass.stableRangeCondition_one_isDedekindFinite

```lean
theorem Bass.stableRangeCondition_one_isDedekindFinite {R : Type u} [Ring R] (h : StableRangeCondition R 1) : IsDedekindFiniteMonoid R
```

Bass's condition `(S_1)` makes every one-sided inverse two-sided.

[Source](../StableRange/Regular.lean#L37-L70) (native database range lines 37–70).

### Bass.isUnit_of_mul_eq_one_of_stableRangeCondition_one

```lean
theorem Bass.isUnit_of_mul_eq_one_of_stableRangeCondition_one {R : Type u} [Ring R] (h : StableRangeCondition R 1) {a b : R} (hab : a * b = 1) : IsUnit a
```

Under `(S_1)`, an element with a right inverse is a unit.

[Source](../StableRange/Regular.lean#L72-L77) (native database range lines 72–77).

### Bass.IsVonNeumannRegular

```lean
def Bass.IsVonNeumannRegular (R : Type u) [Ring R] : Prop
```

A ring is von Neumann-regular when every element has an inner inverse.

[Source](../StableRange/Regular.lean#L79-L81) (native database range lines 79–81).

### Bass.principalRightIdeal

```lean
def Bass.principalRightIdeal {R : Type u} [Ring R] (a : R) : Submodule Rᵐᵒᵖ R
```

The principal right ideal `aR`, represented as a submodule of the right
regular module. The scalar action is `op(b) • y = y * b`.

[Source](../StableRange/Regular.lean#L83-L94) (native database range lines 83–94).

### Bass.mem_principalRightIdeal

```lean
theorem Bass.mem_principalRightIdeal {R : Type u} [Ring R] {a y : R} : y ∈ principalRightIdeal a ↔ ∃ (b : R), a * b = y
```

**API note (not a source docstring):** Membership in the principal right ideal is exactly right multiplication of the generator by a ring element; the right module uses opposite-ring scalars.

[Source](../StableRange/Regular.lean#L96-L99) (native database range lines 96–99).

### Bass.isIdempotentElem_mul_innerInverse

```lean
theorem Bass.isIdempotentElem_mul_innerInverse {R : Type u} [Ring R] {a x : R} (h : a = a * x * a) : IsIdempotentElem (a * x)
```

An inner inverse for `a` makes `a * x` idempotent.

[Source](../StableRange/Regular.lean#L101-L106) (native database range lines 101–106).

### Bass.principalRightIdeals_isCompl_of_isIdempotentElem

```lean
theorem Bass.principalRightIdeals_isCompl_of_isIdempotentElem {R : Type u} [Ring R] {e : R} (he : IsIdempotentElem e) : IsCompl (principalRightIdeal e) (principalRightIdeal (1 - e))
```

The right ideals generated by an idempotent and its complement are
complementary submodules of the right regular module.

[Source](../StableRange/Regular.lean#L108-L135) (native database range lines 108–135).

### Bass.principalRightIdeal_eq_mul_innerInverse

```lean
theorem Bass.principalRightIdeal_eq_mul_innerInverse {R : Type u} [Ring R] {a x : R} (h : a = a * x * a) : principalRightIdeal a = principalRightIdeal (a * x)
```

Multiplying a generator by one of its inner inverses does not change its
principal right ideal.

[Source](../StableRange/Regular.lean#L137-L151) (native database range lines 137–151).

### Bass.principalRightIdeals_isCompl_of_innerInverse

```lean
theorem Bass.principalRightIdeals_isCompl_of_innerInverse {R : Type u} [Ring R] {a x : R} (h : a = a * x * a) : IsCompl (principalRightIdeal a) (principalRightIdeal (1 - a * x))
```

If `x` is an inner inverse for `a`, then `aR` and `(1 - a*x)R` are
complementary principal right ideals.

[Source](../StableRange/Regular.lean#L153-L160) (native database range lines 153–160).

### Bass.IsUnitRegular

```lean
def Bass.IsUnitRegular (R : Type u) [Ring R] : Prop
```

A ring is unit-regular when every element has an inner inverse which is a
unit.

[Source](../StableRange/Regular.lean#L162-L165) (native database range lines 162–165).

### Bass.IsUnitRegular.isVonNeumannRegular

```lean
theorem Bass.IsUnitRegular.isVonNeumannRegular {R : Type u} [Ring R] (h : IsUnitRegular R) : IsVonNeumannRegular R
```

Every unit-regular ring is von Neumann-regular.

[Source](../StableRange/Regular.lean#L167-L172) (native database range lines 167–172).

### Bass.IsVonNeumannRegular.exists_principalRightIdeals_isCompl

```lean
theorem Bass.IsVonNeumannRegular.exists_principalRightIdeals_isCompl {R : Type u} [Ring R] (h : IsVonNeumannRegular R) (a : R) : ∃ (x : R), IsCompl (principalRightIdeal a) (principalRightIdeal (1 - a * x))
```

Every element of a von Neumann-regular ring generates a principal right
ideal with an explicit complementary principal right ideal.

[Source](../StableRange/Regular.lean#L174-L181) (native database range lines 174–181).

### Bass.IsUnitRegular.stableRangeCondition_one

```lean
theorem Bass.IsUnitRegular.stableRangeCondition_one {R : Type u} [Ring R] (h : IsUnitRegular R) : StableRangeCondition R 1
```

Every unit-regular ring satisfies Bass's condition `(S_1)`.

[Source](../StableRange/Regular.lean#L183-L246) (native database range lines 183–246).

### Bass.IsUnitRegular.isDedekindFinite

```lean
theorem Bass.IsUnitRegular.isDedekindFinite {R : Type u} [Ring R] (h : IsUnitRegular R) : IsDedekindFiniteMonoid R
```

Every unit-regular ring is Dedekind-finite.

[Source](../StableRange/Regular.lean#L248-L251) (native database range lines 248–251).

### Bass.not_isUnitRegular_moduleEnd_finsupp_nat

```lean
theorem Bass.not_isUnitRegular_moduleEnd_finsupp_nat (S : Type u) (M : Type v) [Semiring S] [AddCommGroup M] [Module S M] [Nontrivial M] : ¬IsUnitRegular (Module.End S (ℕ →₀ M))
```

The endomorphism ring of a countable direct sum of copies of a nonzero
module is not unit-regular.

[Source](../StableRange/Regular.lean#L253-L278) (native database range lines 253–278).

### Bass.IsUnitRegular.stableRange_one

```lean
theorem Bass.IsUnitRegular.stableRange_one {R : Type u} [Ring R] [Nontrivial R] (h : IsUnitRegular R) : IsStableRange R 1
```

Every nontrivial unit-regular ring has least Bass stable range one.

[Source](../StableRange/Regular.lean#L280-L287) (native database range lines 280–287).

### Bass.isUnitRegular_of_stableRangeCondition_one

```lean
theorem Bass.isUnitRegular_of_stableRangeCondition_one {R : Type u} [Ring R] (hreg : IsVonNeumannRegular R) (hsr : StableRangeCondition R 1) : IsUnitRegular R
```

A von Neumann-regular ring satisfying `(S_1)` is unit-regular.

[Source](../StableRange/Regular.lean#L289-L319) (native database range lines 289–319).

### Bass.isUnitRegular_of_stableRange_one

```lean
theorem Bass.isUnitRegular_of_stableRange_one {R : Type u} [Ring R] (hreg : IsVonNeumannRegular R) (hsr : IsStableRange R 1) : IsUnitRegular R
```

A von Neumann-regular ring with supplied least stable range one is
unit-regular.

[Source](../StableRange/Regular.lean#L321-L327) (native database range lines 321–327).

### Bass.isUnitRegular_iff_stableRangeCondition_one

```lean
theorem Bass.isUnitRegular_iff_stableRangeCondition_one {R : Type u} [Ring R] (hreg : IsVonNeumannRegular R) : IsUnitRegular R ↔ StableRangeCondition R 1
```

For a von Neumann-regular ring, unit-regularity is equivalent to Bass's
condition `(S_1)`.

[Source](../StableRange/Regular.lean#L329-L335) (native database range lines 329–335).

### Bass.isUnitRegular_iff_stableRange_one

```lean
theorem Bass.isUnitRegular_iff_stableRange_one {R : Type u} [Ring R] [Nontrivial R] (hreg : IsVonNeumannRegular R) : IsUnitRegular R ↔ IsStableRange R 1
```

For a nontrivial von Neumann-regular ring, unit-regularity is equivalent
to having least Bass stable range one.

[Source](../StableRange/Regular.lean#L337-L342) (native database range lines 337–342).

## StableRange.Commutative

Scope: mathematical library leaf.

### Bass.IsVonNeumannRegular.isReduced

```lean
theorem Bass.IsVonNeumannRegular.isReduced {R : Type u} [CommRing R] (hreg : IsVonNeumannRegular R) : IsReduced R
```

A commutative von Neumann regular ring has no nonzero nilpotents.

[Source](../StableRange/Commutative.lean#L31-L40) (native database range lines 31–40).

### Bass.IsVonNeumannRegular.krullDimLE_zero

```lean
theorem Bass.IsVonNeumannRegular.krullDimLE_zero {R : Type u} [CommRing R] (hreg : IsVonNeumannRegular R) : Ring.KrullDimLE 0 R
```

Every prime ideal of a commutative von Neumann regular ring is maximal.

[Source](../StableRange/Commutative.lean#L42-L61) (native database range lines 42–61).

### Bass.span_sq_eq_span_of_isReduced_krullDimLE_zero

```lean
theorem Bass.span_sq_eq_span_of_isReduced_krullDimLE_zero {R : Type u} [CommRing R] [IsReduced R] [Ring.KrullDimLE 0 R] (r : R) : Ideal.span {r ^ 2} = Ideal.span {r}
```

In a reduced zero-dimensional commutative ring, the principal ideals
generated by `r` and `r ^ 2` coincide.

[Source](../StableRange/Commutative.lean#L63-L84) (native database range lines 63–84).

### Bass.isVonNeumannRegular_of_isReduced_krullDimLE_zero

```lean
theorem Bass.isVonNeumannRegular_of_isReduced_krullDimLE_zero {R : Type u} [CommRing R] [IsReduced R] [Ring.KrullDimLE 0 R] : IsVonNeumannRegular R
```

A reduced commutative ring of Krull dimension at most zero is von
Neumann regular.

[Source](../StableRange/Commutative.lean#L86-L99) (native database range lines 86–99).

### Bass.isVonNeumannRegular_iff_isReduced_and_krullDimLE_zero

```lean
theorem Bass.isVonNeumannRegular_iff_isReduced_and_krullDimLE_zero {R : Type u} [CommRing R] : IsVonNeumannRegular R ↔ IsReduced R ∧ Ring.KrullDimLE 0 R
```

A commutative ring is von Neumann regular exactly when it is reduced and
has Krull dimension at most zero.

[Source](../StableRange/Commutative.lean#L101-L111) (native database range lines 101–111).

### Bass.flat_of_isReduced_krullDimLE_zero

```lean
theorem Bass.flat_of_isReduced_krullDimLE_zero {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] [IsReduced R] [Ring.KrullDimLE 0 R] : Module.Flat R M
```

Every module over a reduced zero-dimensional commutative ring is flat.

[Source](../StableRange/Commutative.lean#L113-L129) (native database range lines 113–129).

### Bass.IsVonNeumannRegular.flat

```lean
theorem Bass.IsVonNeumannRegular.flat {R : Type u} [CommRing R] (hreg : IsVonNeumannRegular R) (M : Type v) [AddCommGroup M] [Module R M] : Module.Flat R M
```

Every module over a commutative von Neumann regular ring is flat.

[Source](../StableRange/Commutative.lean#L131-L136) (native database range lines 131–136).

## StableRange.CommutativeStableRange

Scope: mathematical library leaf.

### Bass.IsVonNeumannRegular.isUnitRegular

```lean
theorem Bass.IsVonNeumannRegular.isUnitRegular {R : Type u} [CommRing R] (hreg : IsVonNeumannRegular R) : IsUnitRegular R
```

A commutative von Neumann-regular ring is unit-regular.

Starting from an inner inverse `x` of `a`, the reflexive inner inverse
`y = x * a * x` makes `a * y` idempotent. The element
`y + (1 - a * y)` is then a unit, with inverse `a + (1 - a * y)`.

[Source](../StableRange/CommutativeStableRange.lean#L36-L98) (native database range lines 36–98).

### Bass.stableRangeCondition_one_of_krullDimLE_zero

```lean
theorem Bass.stableRangeCondition_one_of_krullDimLE_zero {R : Type u} [CommRing R] [Ring.KrullDimLE 0 R] : StableRangeCondition R 1
```

Every zero-dimensional commutative ring satisfies Bass's condition
`(S₁)`. No reducedness or nontriviality hypothesis is needed.

[Source](../StableRange/CommutativeStableRange.lean#L100-L122) (native database range lines 100–122).

### Bass.stableRange_one_of_krullDimLE_zero

```lean
theorem Bass.stableRange_one_of_krullDimLE_zero {R : Type u} [CommRing R] [Nontrivial R] [Ring.KrullDimLE 0 R] : IsStableRange R 1
```

Every nontrivial zero-dimensional commutative ring has least Bass stable
range one.

[Source](../StableRange/CommutativeStableRange.lean#L124-L132) (native database range lines 124–132).

## StableRange.BassDimension

Scope: mathematical library leaf.

### Bass.isRightUnimodular_iff_span_range_eq_top

```lean
theorem Bass.isRightUnimodular_iff_span_range_eq_top {R : Type u} [CommRing R] {n : ℕ} (row : Fin n → R) : IsRightUnimodular row ↔ Ideal.span (Set.range row) = ⊤
```

Over a commutative ring, a finite row is right-unimodular exactly when
its entries generate the unit ideal.

[Source](../StableRange/BassDimension.lean#L34-L48) (native database range lines 34–48).

### Bass.exists_mem_span_add_avoids_finite_antichain

```lean
theorem Bass.exists_mem_span_add_avoids_finite_antichain {R : Type u} [CommRing R] {n : ℕ} (primes : Finset (Ideal R)) (hprime : ∀ P ∈ primes, P.IsPrime) (hanti : ∀ P ∈ primes, ∀ Q ∈ primes, P ≠ Q → ¬P ≤ Q) (pivot : R) (tail : Fin n → R) (havoid : ∀ P ∈ primes, pivot ∉ P ∨ ∃ (i : Fin n), tail i ∉ P) : ∃ y ∈ Ideal.span (Set.range tail), ∀ P ∈ primes, pivot + y ∉ P
```

A finite-antichain pivot lemma.  If the displayed elements are not all in
any prime in a finite incomparable family, one may add a linear combination of
the tail to the pivot so that the result avoids every prime in the family.

The product coefficients in the proof avoid any hypothesis on the residue
fields.

[Source](../StableRange/BassDimension.lean#L50-L167) (native database range lines 50–167).

### Bass.prefixIdeal

```lean
def Bass.prefixIdeal {R : Type u} [CommRing R] (sequence : ℕ → R) : ℕ → Ideal R
```

The ideal generated by the first `k` terms of a sequence, presented
recursively so that adjoining the next pivot is definitional.

[Source](../StableRange/BassDimension.lean#L169-L172) (native database range lines 169–172).

### Bass.prefixIdeal_zero

```lean
theorem Bass.prefixIdeal_zero {R : Type u} [CommRing R] (sequence : ℕ → R) : prefixIdeal sequence 0 = ⊥
```

**API note (not a source docstring):** The ideal generated by the empty prefix is the bottom ideal.

[Source](../StableRange/BassDimension.lean#L174-L176) (native database range lines 174–176).

### Bass.prefixIdeal_succ

```lean
theorem Bass.prefixIdeal_succ {R : Type u} [CommRing R] (sequence : ℕ → R) (k : ℕ) : prefixIdeal sequence (k + 1) = prefixIdeal sequence k ⊔ Ideal.span {sequence k}
```

**API note (not a source docstring):** The next prefix ideal adjoins the principal ideal generated by the next sequence term.

[Source](../StableRange/BassDimension.lean#L178-L181) (native database range lines 178–181).

### Bass.natCast_le_height_of_mem_minimalPrimes_prefixIdeal

```lean
theorem Bass.natCast_le_height_of_mem_minimalPrimes_prefixIdeal {R : Type u} [CommRing R] (sequence : ℕ → R) (havoid : ∀ (k : ℕ), ∀ P ∈ (prefixIdeal sequence k).minimalPrimes, sequence k ∉ P) (k : ℕ) (P : Ideal R) : P ∈ (prefixIdeal sequence k).minimalPrimes → ↑k ≤ P.height
```

If each new generator avoids every prime minimal over the preceding
prefix, then every prime minimal over the `k`-th prefix has height at least
`k`.

[Source](../StableRange/BassDimension.lean#L183-L220) (native database range lines 183–220).

### Bass.prefixIdeal_eq_top_of_avoids_minimalPrimes

```lean
theorem Bass.prefixIdeal_eq_top_of_avoids_minimalPrimes {R : Type u} [CommRing R] {d : ℕ} [Ring.KrullDimLE d R] (sequence : ℕ → R) (havoid : ∀ (k : ℕ), ∀ P ∈ (prefixIdeal sequence k).minimalPrimes, sequence k ∉ P) : prefixIdeal sequence (d + 1) = ⊤
```

In Krull dimension at most `d`, a sequence of `d + 1` successive pivots
that avoid the minimal primes of every preceding prefix generates the unit
ideal.

[Source](../StableRange/BassDimension.lean#L222-L247) (native database range lines 222–247).

### Bass.natCast_succ_le_height_minimalPrimes_sup_span_singleton

```lean
theorem Bass.natCast_succ_le_height_minimalPrimes_sup_span_singleton {R : Type u} [CommRing R] (I : Ideal R) (k : ℕ) (hheight : ∀ P ∈ I.minimalPrimes, ↑k ≤ P.height) (x : R) (havoid : ∀ P ∈ I.minimalPrimes, x ∉ P) (Q : Ideal R) : Q ∈ (I ⊔ Ideal.span {x}).minimalPrimes → ↑(k + 1) ≤ Q.height
```

Adjoining an element that avoids every minimal prime raises the lower
height bound on the minimal primes by one.

[Source](../StableRange/BassDimension.lean#L249-L275) (native database range lines 249–275).

### Bass.ideal_eq_top_of_natCast_succ_le_height_minimalPrimes

```lean
theorem Bass.ideal_eq_top_of_natCast_succ_le_height_minimalPrimes {R : Type u} [CommRing R] {d : ℕ} [Ring.KrullDimLE d R] (I : Ideal R) (hheight : ∀ P ∈ I.minimalPrimes, ↑(d + 1) ≤ P.height) : I = ⊤
```

An ideal whose minimal primes all have height strictly above the Krull
dimension is the unit ideal.

[Source](../StableRange/BassDimension.lean#L277-L298) (native database range lines 277–298).

### Bass.stableRangeCondition_succ_of_krullDimLE

```lean
theorem Bass.stableRangeCondition_succ_of_krullDimLE {R : Type u} [CommRing R] {d : ℕ} [IsNoetherianRing R] [Ring.KrullDimLE d R] : StableRangeCondition R (d + 1)
```

**Bass's dimension theorem.** A commutative noetherian ring of Krull
dimension at most `d` satisfies Bass's stable-range condition `(S_(d+1))`.

The theorem includes the zero ring and does not require reducedness,
nontriviality, decidable equality, or any hypothesis on residue fields.

[Source](../StableRange/BassDimension.lean#L543-L580) (native database range lines 543–580).

## StableRange.DivisionRing

Scope: mathematical library leaf.

### LinearMap.exists_innerInverse

```lean
theorem LinearMap.exists_innerInverse {K : Type u} [DivisionRing K] {V : Type v} [AddCommGroup V] [Module K V] (f : Module.End K V) : ∃ (g : Module.End K V), f = f * g * f
```

Every endomorphism of a vector space over a division ring has an inner
inverse. No finite-dimensional hypothesis is needed.

[Source](../StableRange/DivisionRing.lean#L35-L73) (native database range lines 35–73).

### LinearMap.exists_linearEquiv_innerInverse

```lean
theorem LinearMap.exists_linearEquiv_innerInverse {K : Type u} [DivisionRing K] {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f : Module.End K V) : ∃ (g : V ≃ₗ[K] V), ∀ (x : V), f (g (f x)) = f x
```

Every endomorphism of a finite-dimensional vector space over a division
ring has an automorphic inner inverse.

[Source](../StableRange/DivisionRing.lean#L77-L106) (native database range lines 77–106).

### Bass.isVonNeumannRegular_moduleEnd

```lean
theorem Bass.isVonNeumannRegular_moduleEnd {K : Type u} [DivisionRing K] {V : Type v} [AddCommGroup V] [Module K V] : IsVonNeumannRegular (Module.End K V)
```

The endomorphism ring of every vector space over a division ring is von
Neumann-regular. No finite-dimensional hypothesis is needed.

[Source](../StableRange/DivisionRing.lean#L115-L119) (native database range lines 115–119).

### Bass.isUnitRegular_matrix

```lean
theorem Bass.isUnitRegular_matrix {K : Type u} [DivisionRing K] {n : Type v} [Fintype n] [DecidableEq n] : IsUnitRegular (Matrix n n K)
```

Every finite square matrix ring over a division ring is unit-regular.

[Source](../StableRange/DivisionRing.lean#L123-L151) (native database range lines 123–151).

## StableRange.RepeatedBlock

Scope: mathematical library leaf.

### Matrix.repeatBlock

```lean
def Matrix.repeatBlock {R : Type u} [NonAssocSemiring R] {m : Type v} {n : Type w} {o : Type x} [DecidableEq o] (A : Matrix m n R) : Matrix (m × o) (n × o) R
```

Repeat a rectangular matrix on diagonal blocks indexed by `o`.

[Source](../StableRange/RepeatedBlock.lean#L34-L36) (native database range lines 34–36).

### Matrix.repeatBlock_eq_kronecker_one

```lean
theorem Matrix.repeatBlock_eq_kronecker_one {R : Type u} [NonAssocSemiring R] {m : Type v} {n : Type w} {o : Type x} [DecidableEq o] (A : Matrix m n R) : A.repeatBlock = kroneckerMap (fun (x1 x2 : R) => x1 * x2) A 1
```

Repeated diagonal blocks are the Kronecker product with an identity
matrix.

[Source](../StableRange/RepeatedBlock.lean#L38-L42) (native database range lines 38–42).

### Matrix.repeatBlockHom

```lean
def Matrix.repeatBlockHom {R : Type u} [NonAssocSemiring R] {m : Type v} {o : Type w} [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o] : Matrix m m R →+* Matrix (m × o) (m × o) R
```

Repeat a square matrix on diagonal blocks, as a ring homomorphism.

[Source](../StableRange/RepeatedBlock.lean#L51-L54) (native database range lines 51–54).

### Matrix.repeatBlockHom_apply

```lean
theorem Matrix.repeatBlockHom_apply {R : Type u} [NonAssocSemiring R] {m : Type v} {o : Type w} [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o] (A : Matrix m m R) : repeatBlockHom A = A.repeatBlock
```

**API note (not a source docstring):** The ring homomorphism that repeats square matrices evaluates to the corresponding repeated-block matrix; its injectivity is a separate theorem requiring nonempty blocks.

[Source](../StableRange/RepeatedBlock.lean#L56-L59) (native database range lines 56–59).

### Matrix.repeatBlockHom_apply_eq_kronecker_one

```lean
theorem Matrix.repeatBlockHom_apply_eq_kronecker_one {R : Type u} [NonAssocSemiring R] {m : Type v} {o : Type w} [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o] (A : Matrix m m R) : repeatBlockHom A = kroneckerMap (fun (x1 x2 : R) => x1 * x2) A 1
```

The repeated-block ring homomorphism is exactly Kronecker product with an
identity matrix.

[Source](../StableRange/RepeatedBlock.lean#L61-L66) (native database range lines 61–66).

### Matrix.repeatBlockHom_injective

```lean
theorem Matrix.repeatBlockHom_injective {R : Type u} [NonAssocSemiring R] {m : Type v} {o : Type w} [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o] [Nonempty o] : Function.Injective ⇑repeatBlockHom
```

Repeating square matrices on a nonempty family of diagonal blocks is
injective.

[Source](../StableRange/RepeatedBlock.lean#L68-L75) (native database range lines 68–75).

## StableRange.DivisionRingRank

Scope: mathematical library leaf.

### Matrix.rowRank

```lean
noncomputable def Matrix.rowRank {K : Type u} [DivisionRing K] {m : Type v} {n : Type w} [Fintype m] [DecidableEq m] (A : Matrix m n K) : ℕ
```

The row rank of a matrix over a possibly noncommutative division ring.

[Source](../StableRange/DivisionRingRank.lean#L41-L43) (native database range lines 41–43).

### Matrix.rowRank_zero

```lean
theorem Matrix.rowRank_zero {K : Type u} [DivisionRing K] {m : Type v} {n : Type w} [Fintype m] [DecidableEq m] : rowRank 0 = 0
```

**API note (not a source docstring):** The zero matrix has row rank zero, including when one of its index types is empty.

[Source](../StableRange/DivisionRingRank.lean#L46-L48) (native database range lines 46–48).

### Matrix.rowRank_one

```lean
theorem Matrix.rowRank_one {K : Type u} [DivisionRing K] {n : Type w} [Fintype n] [DecidableEq n] : rowRank 1 = Fintype.card n
```

**API note (not a source docstring):** The identity matrix has row rank equal to the cardinality of its finite index type, including the empty case.

[Source](../StableRange/DivisionRingRank.lean#L50-L53) (native database range lines 50–53).

### Matrix.rowRank_le_card

```lean
theorem Matrix.rowRank_le_card {K : Type u} [DivisionRing K] {m : Type v} {n : Type w} [Fintype m] [Fintype n] [DecidableEq m] (A : Matrix m n K) : A.rowRank ≤ Fintype.card n
```

**API note (not a source docstring):** Row rank is bounded by the number of columns; it is the dimension of the range of the left-linear row-vector map given by right matrix multiplication.

[Source](../StableRange/DivisionRingRank.lean#L56-L59) (native database range lines 56–59).

### Matrix.rowRank_eq_zero_iff

```lean
theorem Matrix.rowRank_eq_zero_iff {K : Type u} [DivisionRing K] {m : Type v} {n : Type w} [Fintype m] [DecidableEq m] (A : Matrix m n K) : A.rowRank = 0 ↔ A = 0
```

**API note (not a source docstring):** A finite-row matrix over a division ring has row rank zero exactly when it is the zero matrix, even with empty column indices.

[Source](../StableRange/DivisionRingRank.lean#L62-L72) (native database range lines 62–72).

### Matrix.rowRank_pos_iff

```lean
theorem Matrix.rowRank_pos_iff {K : Type u} [DivisionRing K] {m : Type v} {n : Type w} [Fintype m] [DecidableEq m] (A : Matrix m n K) : 0 < A.rowRank ↔ A ≠ 0
```

**API note (not a source docstring):** A finite-row matrix has positive row rank exactly when it is nonzero; empty column indices are allowed.

[Source](../StableRange/DivisionRingRank.lean#L75-L76) (native database range lines 75–76).

### Matrix.rowRank_reindex

```lean
theorem Matrix.rowRank_reindex {K : Type u} [DivisionRing K] {m : Type v} {n : Type w} [Fintype m] [DecidableEq m] {m' : Type x} {n' : Type y} [Fintype m'] [DecidableEq m'] (er : m ≃ m') (ec : n ≃ n') (A : Matrix m n K) : ((reindex er ec) A).rowRank = A.rowRank
```

Independently reindexing the rows and columns of a rectangular matrix does
not change its row rank.

[Source](../StableRange/DivisionRingRank.lean#L109-L115) (native database range lines 109–115).

### Matrix.exists_rowRank_eq

```lean
theorem Matrix.exists_rowRank_eq {K : Type u} [DivisionRing K] {n : Type w} [Fintype n] [DecidableEq n] (k : ℕ) (hk : k ≤ Fintype.card n) : ∃ (A : Matrix n n K), A.rowRank = k
```

Every natural number bounded by the size of a finite square matrix occurs
as the row rank of such a matrix over a division ring.

[Source](../StableRange/DivisionRingRank.lean#L149-L157) (native database range lines 149–157).

### Matrix.rowRank_mul_le_left

```lean
theorem Matrix.rowRank_mul_le_left {K : Type u} [DivisionRing K] {m : Type v} {n : Type w} {p : Type x} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n K) (B : Matrix n p K) : (A * B).rowRank ≤ A.rowRank
```

**API note (not a source docstring):** The row rank of a product is at most the row rank of its left factor, using the left-linear row-vector map defined by right multiplication.

[Source](../StableRange/DivisionRingRank.lean#L160-L163) (native database range lines 160–163).

### Matrix.rowRank_mul_le_right

```lean
theorem Matrix.rowRank_mul_le_right {K : Type u} [DivisionRing K] {m : Type v} {n : Type w} {p : Type x} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n K) (B : Matrix n p K) : (A * B).rowRank ≤ B.rowRank
```

**API note (not a source docstring):** The row rank of a product is at most the row rank of its right factor, using the left-linear row-vector map defined by right multiplication.

[Source](../StableRange/DivisionRingRank.lean#L166-L170) (native database range lines 166–170).

### Matrix.rowRank_add_of_orthogonal_idempotents

```lean
theorem Matrix.rowRank_add_of_orthogonal_idempotents {K : Type u} [DivisionRing K] {n : Type w} [Fintype n] [DecidableEq n] (E G : Matrix n n K) (hEE : E * E = E) (hGG : G * G = G) (hEG : E * G = 0) (hGE : G * E = 0) : (E + G).rowRank = E.rowRank + G.rowRank
```

**API note (not a source docstring):** For mutually annihilating idempotents in a finite square matrix ring over a division ring, row rank is additive.

[Source](../StableRange/DivisionRingRank.lean#L172-L229) (native database range lines 172–229).

### Matrix.rowRank_repeatBlock

```lean
theorem Matrix.rowRank_repeatBlock {K : Type u} [DivisionRing K] {m : Type v} {n : Type w} [Fintype m] [DecidableEq m] {o : Type y} [Fintype o] [DecidableEq o] (A : Matrix m n K) : A.repeatBlock.rowRank = Fintype.card o * A.rowRank
```

Repeating a matrix on `o` diagonal blocks multiplies its row rank by the
number of blocks.

[Source](../StableRange/DivisionRingRank.lean#L317-L324) (native database range lines 317–324).

### Matrix.normalizedRowRank

```lean
noncomputable def Matrix.normalizedRowRank {K : Type u} [DivisionRing K] {n : Type w} [Fintype n] [DecidableEq n] (A : Matrix n n K) : ℝ
```

Row rank divided by the size of a finite square matrix, as a real number.

[Source](../StableRange/DivisionRingRank.lean#L328-L330) (native database range lines 328–330).

### Matrix.exists_normalizedRowRank_eq

```lean
theorem Matrix.exists_normalizedRowRank_eq {K : Type u} [DivisionRing K] {n : Type w} [Fintype n] [DecidableEq n] (k : ℕ) (hk : k ≤ Fintype.card n) : ∃ (A : Matrix n n K), A.normalizedRowRank = ↑k / ↑(Fintype.card n)
```

Every quotient `k / card n` with `k ≤ card n` occurs as the normalized
row rank of a square matrix over a division ring.

[Source](../StableRange/DivisionRingRank.lean#L332-L338) (native database range lines 332–338).

### Matrix.normalizedRowRank_reindex

```lean
theorem Matrix.normalizedRowRank_reindex {K : Type u} [DivisionRing K] {n : Type w} [Fintype n] [DecidableEq n] {n' : Type y} [Fintype n'] [DecidableEq n'] (e : n ≃ n') (A : Matrix n n K) : ((reindex e e) A).normalizedRowRank = A.normalizedRowRank
```

Simultaneously reindexing a finite square matrix does not change its
normalized row rank.

[Source](../StableRange/DivisionRingRank.lean#L344-L349) (native database range lines 344–349).

### Matrix.normalizedRowRank_mem_Icc

```lean
theorem Matrix.normalizedRowRank_mem_Icc {K : Type u} [DivisionRing K] {n : Type w} [Fintype n] [DecidableEq n] [Nonempty n] (A : Matrix n n K) : A.normalizedRowRank ∈ Set.Icc 0 1
```

**API note (not a source docstring):** The normalized row rank lies between zero and one when the finite square index type is nonempty.

[Source](../StableRange/DivisionRingRank.lean#L361-L370) (native database range lines 361–370).

### Matrix.normalizedRowRank_zero

```lean
theorem Matrix.normalizedRowRank_zero {K : Type u} [DivisionRing K] {n : Type w} [Fintype n] [DecidableEq n] : normalizedRowRank 0 = 0
```

**API note (not a source docstring):** The zero matrix has normalized row rank zero, including for the empty index type.

[Source](../StableRange/DivisionRingRank.lean#L373-L376) (native database range lines 373–376).

### Matrix.normalizedRowRank_one

```lean
theorem Matrix.normalizedRowRank_one {K : Type u} [DivisionRing K] {n : Type w} [Fintype n] [DecidableEq n] [Nonempty n] : normalizedRowRank 1 = 1
```

**API note (not a source docstring):** The identity has normalized row rank one when its finite index type is nonempty; the empty-matrix case is not covered.

[Source](../StableRange/DivisionRingRank.lean#L378-L381) (native database range lines 378–381).

### Matrix.normalizedRowRank_pos_iff

```lean
theorem Matrix.normalizedRowRank_pos_iff {K : Type u} [DivisionRing K] {n : Type w} [Fintype n] [DecidableEq n] [Nonempty n] (A : Matrix n n K) : 0 < A.normalizedRowRank ↔ A ≠ 0
```

**API note (not a source docstring):** For nonempty finite square matrices, normalized row rank is positive exactly when the matrix is nonzero.

[Source](../StableRange/DivisionRingRank.lean#L383-L386) (native database range lines 383–386).

### Matrix.normalizedRowRank_mul_le_left

```lean
theorem Matrix.normalizedRowRank_mul_le_left {K : Type u} [DivisionRing K] {n : Type w} [Fintype n] [DecidableEq n] [Nonempty n] (A B : Matrix n n K) : (A * B).normalizedRowRank ≤ A.normalizedRowRank
```

**API note (not a source docstring):** For nonempty finite square matrices, the normalized row rank of a product is at most that of its left factor.

[Source](../StableRange/DivisionRingRank.lean#L388-L391) (native database range lines 388–391).

### Matrix.normalizedRowRank_mul_le_right

```lean
theorem Matrix.normalizedRowRank_mul_le_right {K : Type u} [DivisionRing K] {n : Type w} [Fintype n] [DecidableEq n] [Nonempty n] (A B : Matrix n n K) : (A * B).normalizedRowRank ≤ B.normalizedRowRank
```

**API note (not a source docstring):** For nonempty finite square matrices, the normalized row rank of a product is at most that of its right factor.

[Source](../StableRange/DivisionRingRank.lean#L393-L396) (native database range lines 393–396).

### Matrix.normalizedRowRank_add_of_orthogonal_idempotents

```lean
theorem Matrix.normalizedRowRank_add_of_orthogonal_idempotents {K : Type u} [DivisionRing K] {n : Type w} [Fintype n] [DecidableEq n] (E G : Matrix n n K) (hEE : E * E = E) (hGG : G * G = G) (hEG : E * G = 0) (hGE : G * E = 0) : (E + G).normalizedRowRank = E.normalizedRowRank + G.normalizedRowRank
```

**API note (not a source docstring):** For two mutually annihilating idempotent square matrices, normalized row rank is additive; this equality also holds with an empty index type.

[Source](../StableRange/DivisionRingRank.lean#L399-L406) (native database range lines 399–406).

### Matrix.normalizedRowRank_repeatBlock

```lean
theorem Matrix.normalizedRowRank_repeatBlock {K : Type u} [DivisionRing K] {n : Type w} [Fintype n] [DecidableEq n] [Nonempty n] {o : Type y} [Fintype o] [DecidableEq o] [Nonempty o] (A : Matrix n n K) : A.repeatBlock.normalizedRowRank = A.normalizedRowRank
```

Repeating a nonempty square matrix on a nonempty finite family of diagonal
blocks preserves its normalized row rank.

[Source](../StableRange/DivisionRingRank.lean#L410-L421) (native database range lines 410–421).

## StableRange.Cancellation

Scope: mathematical library leaf.

### Bass.exists_linearEquiv_of_prod_of_end_stableRangeCondition_one

```lean
theorem Bass.exists_linearEquiv_of_prod_of_end_stableRangeCondition_one {R : Type u} [Ring R] {M : Type v} {A : Type w} {B : Type x} [AddCommGroup M] [AddCommGroup A] [AddCommGroup B] [Module R M] [Module R A] [Module R B] (h : StableRangeCondition (Module.End R M) 1) (e : (M × A) ≃ₗ[R] M × B) : Nonempty (A ≃ₗ[R] B)
```

A module whose endomorphism ring satisfies `(S₁)` cancels from a binary
product. No finiteness or projectivity assumption is required.

[Source](../StableRange/Cancellation.lean#L33-L150) (native database range lines 33–150).

### Bass.subsingleton_of_pi_linearEquiv_pi_prod

```lean
theorem Bass.subsingleton_of_pi_linearEquiv_pi_prod {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] {P : Type x} [AddCommGroup P] [Module R P] (h : StableRangeCondition (Module.End R M) 1) (n : ℕ) (e : (Fin n → M) ≃ₗ[R] (Fin n → M) × P) : Subsingleton P
```

If the endomorphism ring of `M` satisfies `(S₁)`, a finite free power of
`M` cannot absorb a nontrivial complementary module.

[Source](../StableRange/Cancellation.lean#L152-L179) (native database range lines 152–179).

### Bass.IsUnitRegular.subsingleton_of_fin_linearEquiv_fin_prod

```lean
theorem Bass.IsUnitRegular.subsingleton_of_fin_linearEquiv_fin_prod {R : Type u} [Ring R] {P : Type x} [AddCommGroup P] [Module Rᵐᵒᵖ P] (h : IsUnitRegular R) (n : ℕ) (e : (Fin n → R) ≃ₗ[Rᵐᵒᵖ] (Fin n → R) × P) : Subsingleton P
```

A unit-regular ring satisfies the finite-free cancellation condition for
its regular right module. In Lean this right module is a left module over the
opposite ring.

[Source](../StableRange/Cancellation.lean#L181-L190) (native database range lines 181–190).

## StableRange.RowKernel

Scope: mathematical library leaf.

### Bass.coefficientRowMatrix

```lean
def Bass.coefficientRowMatrix (R : Type u) (n : ℕ) (a : Fin n → R) : Matrix (Fin 1) (Fin n) R
```

A finite coefficient row, regarded as a one-row matrix.

[Source](../StableRange/RowKernel.lean#L33-L36) (native database range lines 33–36).

### Bass.coefficientRowLinearMap

```lean
def Bass.coefficientRowLinearMap (R : Type u) [CommRing R] (n : ℕ) (a : Fin n → R) : (Fin n → R) →ₗ[R] Fin 1 → R
```

The linear functional represented by a finite coefficient row.

[Source](../StableRange/RowKernel.lean#L38-L42) (native database range lines 38–42).

### Bass.coefficientRowLinearMap_apply

```lean
theorem Bass.coefficientRowLinearMap_apply (R : Type u) [CommRing R] (n : ℕ) (a x : Fin n → R) : (coefficientRowLinearMap R n a) x 0 = a ⬝ᵥ x
```

**API note (not a source docstring):** Evaluation of the one-row matrix map at its unique output index is the row dot product. This statement is over a commutative ring.

[Source](../StableRange/RowKernel.lean#L44-L47) (native database range lines 44–47).

### Bass.isRightUnimodular_iff_surjective_coefficientRowLinearMap

```lean
theorem Bass.isRightUnimodular_iff_surjective_coefficientRowLinearMap (R : Type u) [CommRing R] (n : ℕ) (a : Fin n → R) : IsRightUnimodular a ↔ Function.Surjective ⇑(coefficientRowLinearMap R n a)
```

A finite row is right-unimodular exactly when its coefficient functional
onto one copy of the ring is surjective.

[Source](../StableRange/RowKernel.lean#L49-L72) (native database range lines 49–72).

### Bass.coefficientRowScalarMap

```lean
def Bass.coefficientRowScalarMap (R : Type u) [CommRing R] (n : ℕ) (a : Fin n → R) : (Fin n → R) →ₗ[R] R
```

The scalar-valued version of a coefficient row.

[Source](../StableRange/RowKernel.lean#L74-L77) (native database range lines 74–77).

### Bass.coefficientRowScalarMap_apply

```lean
theorem Bass.coefficientRowScalarMap_apply (R : Type u) [CommRing R] (n : ℕ) (a x : Fin n → R) : (coefficientRowScalarMap R n a) x = a ⬝ᵥ x
```

**API note (not a source docstring):** The scalar-valued coefficient map evaluates to the row dot product.

[Source](../StableRange/RowKernel.lean#L79-L83) (native database range lines 79–83).

### Bass.ker_coefficientRowScalarMap_eq

```lean
theorem Bass.ker_coefficientRowScalarMap_eq (R : Type u) [CommRing R] (n : ℕ) (a : Fin n → R) : (coefficientRowScalarMap R n a).ker = (coefficientRowLinearMap R n a).ker
```

**API note (not a source docstring):** The kernels of the scalar-valued map and its equivalent one-coordinate function-valued version agree.

[Source](../StableRange/RowKernel.lean#L85-L98) (native database range lines 85–98).

### Bass.coefficientRowConsMap

```lean
def Bass.coefficientRowConsMap (R : Type u) [CommRing R] (n : ℕ) (a₀ : R) (a : Fin n → R) : R × (Fin n → R) →ₗ[R] R
```

A split coefficient row, with its leading coordinate separated from its
tail.

[Source](../StableRange/RowKernel.lean#L100-L106) (native database range lines 100–106).

### Bass.coefficientRowConsMap_apply

```lean
theorem Bass.coefficientRowConsMap_apply (R : Type u) [CommRing R] (n : ℕ) (a₀ : R) (a : Fin n → R) (x : R × (Fin n → R)) : (coefficientRowConsMap R n a₀ a) x = a₀ * x.1 + a ⬝ᵥ x.2
```

**API note (not a source docstring):** The separated coefficient functional evaluates at a pair by multiplying the leading coordinate and adding the tail dot product; the coefficients remain on the left in this commutative-ring map.

[Source](../StableRange/RowKernel.lean#L108-L113) (native database range lines 108–113).

### Bass.kernelEquivOfLinearEquiv

```lean
noncomputable def Bass.kernelEquivOfLinearEquiv {R : Type u_1} {A : Type u_2} {B : Type u_3} {C : Type u_4} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (f : A →ₗ[R] C) (g : B →ₗ[R] C) (e : A ≃ₗ[R] B) (h : ∀ (x : A), g (e x) = f x) : ↥f.ker ≃ₗ[R] ↥g.ker
```

Transporting the domain of a linear map by a linear equivalence transports
its kernel.  This explicit form is convenient when the conjugacy is proved
pointwise rather than as an equality of bundled maps.

[Source](../StableRange/RowKernel.lean#L115-L133) (native database range lines 115–133).

### Bass.coordinateHyperplaneEquiv

```lean
noncomputable def Bass.coordinateHyperplaneEquiv (R : Type u) [Semiring R] (n : ℕ) (i : Fin n) : ↥(LinearMap.proj i).ker ≃ₗ[R] { j : Fin n // j ≠ i } → R
```

The coordinate hyperplane where the `i`th coordinate vanishes is the
function module on the remaining indices. This specializes mathlib's
equivalence for intersections of kernels of coordinate projections.

[Source](../StableRange/RowKernel.lean#L135-L154) (native database range lines 135–154).

### Bass.coefficientRowKernelEquivOfMatrixInverse

```lean
noncomputable def Bass.coefficientRowKernelEquivOfMatrixInverse (R : Type u) [CommRing R] (n : ℕ) (i : Fin n) (a : Fin n → R) (A B : Matrix (Fin n) (Fin n) R) (hrow : A i = a) (hAB : A * B = 1) (hBA : B * A = 1) : ↥(coefficientRowLinearMap R n a).ker ≃ₗ[R] { j : Fin n // j ≠ i } → R
```

If `A` has the specified two-sided inverse `B` and its `i`th row is `a`,
then the kernel of the coefficient row `a` is explicitly equivalent to the
free module on the column indices other than `i`.

[Source](../StableRange/RowKernel.lean#L156-L180) (native database range lines 156–180).

### Bass.free_ker_coefficientRowLinearMap_of_matrix_inverse

```lean
theorem Bass.free_ker_coefficientRowLinearMap_of_matrix_inverse (R : Type u) [CommRing R] (n : ℕ) (i : Fin n) (a : Fin n → R) (A B : Matrix (Fin n) (Fin n) R) (hrow : A i = a) (hAB : A * B = 1) (hBA : B * A = 1) : Module.Free R ↥(coefficientRowLinearMap R n a).ker
```

A coefficient row occurring as any distinguished row of an explicitly
invertible square matrix has free kernel.

[Source](../StableRange/RowKernel.lean#L182-L191) (native database range lines 182–191).

### Bass.kernelProdEquivOfRightInverse

```lean
noncomputable def Bass.kernelProdEquivOfRightInverse {R : Type u_1} {A : Type u_2} {B : Type u_3} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] (f : A →ₗ[R] B) (g : B →ₗ[R] A) (hfg : f ∘ₗ g = LinearMap.id) : (↥f.ker × B) ≃ₗ[R] A
```

The usual split-kernel equivalence for a map with a specified right
inverse.

[Source](../StableRange/RowKernel.lean#L193-L212) (native database range lines 193–212).

### Bass.kernelProdEquivOfIsRightUnimodular

```lean
noncomputable def Bass.kernelProdEquivOfIsRightUnimodular (R : Type u) [CommRing R] (n : ℕ) (a : Fin n → R) (ha : IsRightUnimodular a) : (↥(coefficientRowScalarMap R n a).ker × R) ≃ₗ[R] Fin n → R
```

A right-unimodular coefficient row has the standard split presentation of
its kernel.

[Source](../StableRange/RowKernel.lean#L214-L232) (native database range lines 214–232).

### Bass.coefficientRowConsKernelEquivOfStableRangeCondition

```lean
noncomputable def Bass.coefficientRowConsKernelEquivOfStableRangeCondition (R : Type u) [CommRing R] (n : ℕ) (hstable : StableRangeCondition R n) (a₀ : R) (a : Fin n → R) (ha : IsRightUnimodularCons a₀ a) : ↥(coefficientRowConsMap R n a₀ a).ker ≃ₗ[R] Fin n → R
```

The explicit two-shear equivalence from the kernel of a right-unimodular
split row to the shortened finite free module. The first shear replaces the
tail by the stable-reduced row, and the second uses a unimodular witness for
that row to kill the leading coefficient.

[Source](../StableRange/RowKernel.lean#L234-L295) (native database range lines 234–295).

### Bass.free_ker_coefficientRowConsMap_of_stableRangeCondition

```lean
theorem Bass.free_ker_coefficientRowConsMap_of_stableRangeCondition (R : Type u) [CommRing R] (n : ℕ) (hstable : StableRangeCondition R n) (a₀ : R) (a : Fin n → R) (ha : IsRightUnimodularCons a₀ a) : Module.Free R ↥(coefficientRowConsMap R n a₀ a).ker
```

Bass stable range turns a right-unimodular split row into a kernel which is
free.

[Source](../StableRange/RowKernel.lean#L297-L306) (native database range lines 297–306).

### Bass.coefficientRowKernelEquivSuccOfStableRangeCondition

```lean
noncomputable def Bass.coefficientRowKernelEquivSuccOfStableRangeCondition (R : Type u) [CommRing R] (n : ℕ) (hstable : StableRangeCondition R n) (a : Fin (n + 1) → R) (ha : IsRightUnimodular a) : ↥(coefficientRowLinearMap R (n + 1) a).ker ≃ₗ[R] Fin n → R
```

At the literal stable-range length, the kernel of a right-unimodular
coefficient row is explicitly equivalent to the shortened finite free
module.

[Source](../StableRange/RowKernel.lean#L308-L333) (native database range lines 308–333).

### Bass.free_ker_coefficientRowLinearMap_succ_of_stableRangeCondition

```lean
theorem Bass.free_ker_coefficientRowLinearMap_succ_of_stableRangeCondition (R : Type u) [CommRing R] (n : ℕ) (hstable : StableRangeCondition R n) (a : Fin (n + 1) → R) (ha : IsRightUnimodular a) : Module.Free R ↥(coefficientRowLinearMap R (n + 1) a).ker
```

At the literal stable-range length, the kernel of a right-unimodular
coefficient row is free.

[Source](../StableRange/RowKernel.lean#L335-L344) (native database range lines 335–344).

### Bass.free_ker_coefficientRowLinearMap_of_stableRangeCondition

```lean
theorem Bass.free_ker_coefficientRowLinearMap_of_stableRangeCondition (R : Type u) [CommRing R] (s n : ℕ) (hstable : StableRangeCondition R s) (a : Fin n → R) (ha : IsRightUnimodular a) (hn : s + 1 ≤ n) : Module.Free R ↥(coefficientRowLinearMap R n a).ker
```

If `(S_s)` holds, every right-unimodular coefficient row of length at
least `s + 1` has free kernel.

[Source](../StableRange/RowKernel.lean#L346-L358) (native database range lines 346–358).

## StableRange

Scope: aggregate public-import root.

No native public display sites in this module.

## PublicAPIClient

Scope: private regression client (not exported by the library).

No native public display sites in this module.
