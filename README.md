# stable-range

Reusable Lean theory of Bass stable range, unimodular rows, and applications.

The mathematical API is source-independent; interpretation and coverage of
motivating sources live in their source repositories. Import `StableRange` for
the complete library, or import individual leaves below.

## Headline results

These results build on Mathlib's algebraic APIs. The quasiregular-ideal
predicate and unit characterization are imported from the pinned
`general-linear-groups` dependency; the proved stable-range consequences are
developed here. Each link points to a declaration in this repository.

### Bass conditions, quotients and local rings

For arbitrary possibly noncommutative rings, the library defines finite
[right-unimodular rows](StableRange/Basic.lean#L38),
[Bass's `(S_n)` condition](StableRange/Basic.lean#L62), and
[relational least stable range](StableRange/Basic.lean#L162). It proves
[monotonicity](StableRange/Basic.lean#L150), invariance under ring equivalence,
[descent along surjective homomorphisms](StableRange/Quotient.lean#L62), and
[equivalence under quotients by quasiregular two-sided ideals](StableRange/Quotient.lean#L135).
[Nontrivial local rings have least stable range one](StableRange/Local.lean#L132).
The zero ring can satisfy `(S_0)`; this is not a least-index-one assertion.
Witnesses multiply on the right, and reduction order matters outside
commutative rings; see [Scope and conventions](#scope-and-conventions).

[Dependent products](StableRange/Product.lean) preserve `(S_n)` for arbitrary
index sets and row lengths. [Semisimple rings](StableRange/Semisimple.lean)
satisfy `(S_1)`, as do rings with a semisimple quotient by the Jacobson radical;
nilpotence of the radical is not required.
For any ring satisfying `(S₁)`, [finite square matrix rings](StableRange/Matrix.lean)
also satisfy `(S₁)`, including empty indices and the zero ring. For nonempty finite
indices, the matrix ring satisfies `(S₁)` **if and only if** its coefficient ring
does, for arbitrary possibly noncommutative rings; empty indices need not reflect
`(S₁)`.
For any idempotent `e` in such a ring, [its corner `eRe`](StableRange/Corner.lean#L35)
also satisfies `(S₁)`, with identity `e`. This needs neither centrality nor
fullness and includes `e = 0`, `e = 1` and zero rings.

The [commutative semilocal `(S₁)` theorem](StableRange/Semilocal.lean)
uses `[Finite (MaximalSpectrum R)]`, with no nontriviality, locality,
Noetherianity or dimension bound. Finite Chinese remaindering chooses a
coefficient that makes the shortened entry avoid every maximal ideal, hence
a unit. For a distinguished entry `a` and right-unimodular pair `(a, b)`,
the shortening is `b - a * t`, even when the maximal spectrum is empty.

### Regular rings and module cancellation

`(S_1)` implies [direct finiteness](StableRange/Regular.lean#L46), and
is [equivalent to unit-valued shortening](StableRange/Regular.lean#L88)
of every right-unimodular pair. For arbitrary rings, including the zero ring,
[`(S_1)` is invariant under passage to the opposite ring](StableRange/Opposite.lean).
It follows that the same condition supports unit-valued left-ordered shortening.
Under von Neumann regularity it is
[equivalent to unit-regularity](StableRange/Regular.lean#L365).
An inner inverse constructs
[complementary principal right ideals](StableRange/Regular.lean#L185).
If the endomorphism ring of a module `M` satisfies `(S_1)`, then
[`M` cancels from binary direct products](StableRange/Cancellation.lean#L44):
`M × A ≃ M × B` implies `A ≃ B`, without finiteness or projectivity
assumptions. For the regular right module, the statement uses the **opposite
ring**. [Finite powers](StableRange/Cancellation.lean#L193) over a unit-regular
ring cannot absorb a nontrivial complementary module.

### Endomorphisms and matrices over division rings

Endomorphisms of arbitrary vector spaces over division rings have
[inner inverses](StableRange/DivisionRing.lean#L45), hence von Neumann-regular
endomorphism rings. In finite dimension the inner inverse can be
[an automorphism](StableRange/DivisionRing.lean#L87), yielding
[unit-regular finite square matrix rings](StableRange/DivisionRing.lean#L133),
including empty indices. By contrast, the endomorphism ring of a countable
direct sum of copies of [any nonzero additive module](StableRange/Regular.lean#L287)
is not unit-regular; the sum need not be a free module.

### Row rank and repeated diagonal blocks

For division-ring coefficients, [row rank](StableRange/DivisionRingRank.lean#L49)
is the finrank of the image of the **left-linear row-vector map given by
right multiplication**. Rectangular ranks have multiplication bounds,
orthogonal-idempotent additivity and independent row/column reindexing.
For square matrices, [normalized rank](StableRange/DivisionRingRank.lean#L338)
is real row rank divided by index cardinality; identity rank one and positive
bounds require a nonempty index. Every allowed
[natural rank](StableRange/DivisionRingRank.lean#L158) and
[normalized value](StableRange/DivisionRingRank.lean#L343) is realized.
[Rectangular repeated blocks](StableRange/DivisionRingRank.lean#L327) scale
rank by the block count; normalized square rank is
[unchanged](StableRange/DivisionRingRank.lean#L421) for nonempty matrix and
block indices. Empty square matrices have normalized rank zero.

Separately, over arbitrary potentially nonassociative/noncommutative
`NonAssocSemiring` coefficients, [`Matrix.repeatBlockHom`](StableRange/RepeatedBlock.lean#L59)
is a ring homomorphism, [injective](StableRange/RepeatedBlock.lean#L77)
when the block family is nonempty.

### Commutative regularity and dimension bounds

A commutative ring is von Neumann regular
[iff it is reduced and has Krull dimension at most zero](StableRange/Commutative.lean#L111).
[All its modules are flat](StableRange/Commutative.lean#L142), with no finite or
Noetherian hypothesis. A commutative ring of dimension at most zero
[satisfies `(S_1)`](StableRange/CommutativeStableRange.lean#L112) even without
reducedness or nontriviality; *least* stable index one requires `Nontrivial`.
Every commutative von Neumann-regular ring is unit-regular.

More generally, a commutative Noetherian ring with `Ring.KrullDimLE d`
[satisfies `(S_(d+1))`](StableRange/BassDimension.lean#L560), proved by finite
prime avoidance and minimal-prime height induction, without an infinite-residue-
fields premise.

### Coefficient-row splittings and free kernels

For any ring `R`, a finite row `a : Fin n → R` defines a right-linear map over
`Rᵐᵒᵖ` by `σ(x) = ∑ i, a i * x i`. [Right-unimodularity](StableRange/RowKernel.lean#L509)
is equivalent to surjectivity; equivalently, the map admits a section and the
entries' [right span](StableRange/RowKernel.lean#L558) is the whole module. A
witness column `b` with `∑ i, a i * b i = 1` gives the
[section](StableRange/RowKernel.lean#L418) `y ↦ (fun i => b i * y)` and an
[explicit kernel-product equivalence](StableRange/RowKernel.lean#L454)
`ker σ × R ≃ₗ[Rᵐᵒᵖ] (Fin n → R)`. Its inverse second coordinate is `σ`, and the
[converse](StableRange/RowKernel.lean#L582) requires this original-row identity,
not merely an abstract equivalence. Empty rows and the zero ring are included,
without stable-range or commutativity hypotheses. For commutative rings,
[kernel transport](StableRange/RowKernel.lean#L623) and the
[comparison](StableRange/RowKernel.lean#L664) use the same chosen witness in
both splittings.

For a right-unimodular row, the splitting makes its kernel finitely generated;
[right-unimodularity together with kernel freeness](StableRange/RightRowCompletion.lean)
is equivalent to the existence of two-sided rectangular inverse matrices
`A : Matrix (Fin (m + 1)) (Fin n) R` and
`B : Matrix (Fin n) (Fin (m + 1)) R` with first row `A 0 = a`.
A supplied witness `b` and supplied kernel coordinates construct these matrices
with first column of `B` equal to `b`: forward coordinates are `σ(x)` followed
by the selected coordinates of `x - (fun i => b i * σ(x))`, and inverse
coordinates reconstruct `b i * y 0` plus the kernel column. Conversely, the
matrix pair gives the explicit kernel coordinates `k ↦ Fin.tail (A *ᵥ k)`
with inverse `t ↦ B *ᵥ Fin.cons 0 t`, without assuming freeness. These are
right-linear **column** actions for arbitrary rings; neither square size nor
invariant basis number is assumed. An independent `M₂(ℤ)` client checks a
nonzero kernel column and a noncentral multiplication order.

Over a commutative ring satisfying `(S_s)`, a right-unimodular coefficient
row of length at least `s + 1`
[has a free kernel](StableRange/RowKernel.lean#L361), by explicit two-shear
reduction. Independently of stable range, a *chosen row* of a square matrix
with an actual two-sided inverse has
[an explicit free-kernel equivalence](StableRange/RowKernel.lean#L171) with the
function module on complementary column indices. Both inverse identities
and an actual row index are required, not a merely proposed inverse.

For a commutative ring and a specified two-element Bézout witness
`a₀b₀ + a₁b₁ = 1`, [explicit completion](StableRange/RowCompletionTwo.lean)
has matrix rows `(a₀,a₁)` and `(-b₁,b₀)`, with an explicit inverse and
original first-coordinate functional. The resulting kernel coordinate is
`-b₁x₀ + b₀x₁`, whose inverse sends `t` to `(-a₁t,a₀t)`. A supplied
`(Fin 2 → R) ≃ₗ[R] (R × P)` therefore gives `P ≃ₗ[R] R` through its
original first projection, without a stable-range or freeness hypothesis on
`P`. This commutative left-linear construction includes the zero ring; it
does not assert arbitrary-rank or noncommutative row completion.

### Finite-free cancellation and first-row completion

Over a commutative ring satisfying `(S_s)`, an explicit presentation
`P × (Fin m → R) ≃ₗ[R] (Fin (n + m) → R)` with `s ≤ n`
[cancels the finite free summand](StableRange/FiniteFree.lean#L47), giving
`P ≃ₗ[R] (Fin n → R)` and hence `Module.Free R P`. The module `P` may live
in a different universe from `R`; it need not already be free. Noetherian
Krull-dimension-upper-bound specializations state their additional hypotheses
separately. The exact coordinate count applies even to the zero ring; it does
not claim that different free presentations have a unique rank.

For a right-unimodular row `a : Fin (n + 1) → R` under the same `(S_s)` and
`s ≤ n` bound, [first-row completion](StableRange/RowCompletion.lean#L44)
constructs a linear self-equivalence whose zeroth output coordinate on `x`
equals `a ⬝ᵥ x`. Its matrix has literal first row `a` and an explicit
[two-sided inverse](StableRange/RowCompletion.lean#L134). Here too the zero
ring is allowed; the dimension-bound form separately requires Noetherianity.

### Elementary diagonalization under `(S₁)`

For a commutative ring satisfying Bass's `(S₁)`, an elementary left factor
[makes the leading entry a unit](StableRange/ElementaryGeneration.lean#L40)
in every invertible successor-rank matrix. The resulting
[two-sided elementary diagonalization](StableRange/ElementaryGeneration.lean#L93)
applies to every invertible `Fin n` matrix, including `n = 0`, and
[transports to arbitrary finite decidable index types](StableRange/ElementaryGeneration.lean#L104).
The proofs reuse the rectangular elementary shear, its first-column action,
and the conditional all-rank unit-pivot induction from `general-linear-groups`.
The condition is `(S₁)`, not a least-index-one assertion: it covers the zero
ring as well as local and nonlocal examples, without requiring `Nontrivial` or
locality. The diagonalization also supplies the determinant-one
characterization below.

### Determinants and elementary quotients under `(S₁)`

[`DeterminantGeneration`](StableRange/DeterminantGeneration.lean) proves that
an invertible finite matrix is elementary iff its determinant is one, and that
the stable elementary subgroup is the kernel of the stable determinant, over
any commutative ring satisfying `(S₁)`. It gives a quotient-to-units equivalence
whose forward map is the existing quotient determinant and whose inverse is the
existing rank-one section, with coefficient-map and local-ring comparison laws.
The finite proof uses elementary two-sided diagonalization and the fact that
a diagonal of units with product one is elementary. The stable and quotient
results use finite-stage representatives and the rank-one section.
The statements impose neither locality nor a nontriviality or positive-rank
hypothesis. In particular, no general-ring determinant-one generation is claimed.

## Public interface and use

Use ordinary `import StableRange` for the complete interface, or import a leaf
below. The root publicly re-exports the listed leaves. The tests are not imported
by the root and add no public library declarations.

| Module (under `StableRange`) | Representative interface |
| --- | --- |
| `Basic` | `Bass.IsRightUnimodular`, `StableRangeCondition`, `IsStableRange`; monotonicity and equivalence |
| `Quotient` | `stableRangeCondition_of_surjective`, `stableRangeCondition_quotient_iff` |
| `Local` | `stableRangeCondition_one_of_isLocalRing`, `stableRange_one_of_isLocalRing` |
| `Semilocal` | commutative finite-maximal-spectrum `(S₁)` via Chinese remaindering |
| `Regular` | unit-valued pair shortening, `IsVonNeumannRegular`, `IsUnitRegular`, complementary principal right ideals and shift counterexample |
| `Matrix` | finite square-matrix preservation of `(S₁)` over arbitrary rings |
| `Corner` | `(S₁)` for the corner of any idempotent in a ring satisfying `(S₁)` |
| `Opposite` | `stableRangeCondition_one_opposite`, `stableRangeCondition_one_opposite_iff` |
| `DivisionRing` | `LinearMap.exists_innerInverse`, `exists_linearEquiv_innerInverse`, matrix unit-regularity |
| `Product` | dependent-product preservation of `(Sₙ)` |
| `Semisimple` | `(S₁)` for semisimple rings and rings with semisimple Jacobson-radical quotient |
| `RepeatedBlock` | `Matrix.repeatBlock`, `repeatBlockHom`, Kronecker formula and injectivity |
| `DivisionRingRank` | `Matrix.rowRank`, `normalizedRowRank`, reindexing, realization and repeated blocks |
| `Commutative` | regular iff reduced and dimension at most zero; arbitrary-module flatness |
| `CommutativeStableRange` | zero-dimensional stable range; commutative regular implies unit-regular |
| `BassDimension` | finite-prime avoidance, prefix-ideal height bounds, `stableRangeCondition_succ_of_krullDimLE` |
| `Cancellation` | `exists_linearEquiv_of_prod_of_end_stableRangeCondition_one` and finite-power consequences |
| `RowKernel` | `kernelEquivOfLinearEquiv`, arbitrary-ring right-linear coefficient rows and split kernels; commutative free-kernel equivalences |
| `RightRowCompletion` | supplied right-linear kernel coordinates and two-sided rectangular inverse matrices; converse kernel equivalence and free-kernel criterion |
| `RowCompletionTwo` | supplied-witness `SL(2, R)` row completion, scalar kernel coordinates and supplied-product cancellation over commutative rings |
| `FiniteFree` | explicit finite-free summand cancellation and exact-size freeness under `(S_s)` or a noetherian dimension bound |
| `RowCompletion` | first-coordinate equivalence, completed matrix and two-sided inverse under `(S_s)` or a noetherian dimension bound |
| `ElementaryGeneration` | commutative `(S₁)` elementary unit pivots, diagonalization of `Fin n` matrices and finite reindexing |
| `DeterminantGeneration` | finite determinant-one membership, stable determinant kernel and quotient-to-units equivalence under commutative `(S₁)` |

Names without an explicit namespace in the table are in `Bass`, except the
division-ring and matrix entries as indicated. The [historical generated API](docs/API.md)
shows all 121 native mathematical-leaf display sites, their complete visible
signatures and 23 labeled authored notes for missing source docstrings.
The [generation guide](docs/README.md) explains its scope and exact snapshot;
[documentation credits](docs/CREDITS.md) record the reused adapter expression.
The aggregate root and historical regression client are included as zero-site
module records. This complete example uses only
the ordinary root import:

```lean
module
import StableRange

example (R : Type*) [CommRing R] [IsNoetherianRing R]
    (d : ℕ) [Ring.KrullDimLE d R] : Bass.StableRangeCondition R (d + 1) :=
  Bass.stableRangeCondition_succ_of_krullDimLE

example (R : Type*) [CommRing R] (s n : ℕ)
    (hs : Bass.StableRangeCondition R s) (a : Fin n → R)
    (ha : Bass.IsRightUnimodular a) (hn : s + 1 ≤ n) :
    Module.Free R (LinearMap.ker (Bass.coefficientRowLinearMap R n a)) :=
  Bass.free_ker_coefficientRowLinearMap_of_stableRangeCondition R s n hs a ha hn
```

`tests/StableRangeTests/PublicAPIClient.lean` checks the ordinary root import
with private regression proofs and the public zero-ring fixture
`StableRangePublicAPIClient.zero_ring_condition`, which is not a production
result. Its two extra Mathlib imports supply concrete `ZMod` fixtures and the
Artinian dimension instance, not another route to project API. It covers every
module family,
independent universes, opposite division rings, nonassociative repeated-block
coefficients, zero/empty boundaries, and a nonreduced ring. It is part of the
default build. The second default client,
`tests/StableRangeTests/ElementaryGenerationClient.lean`, independently checks
empty-rank, rank-one and zero-ring boundaries and a nonlocal `(S₁)` example
with an explicit elementary shear producing a unit pivot. The rank-one
boundary is the public test fixture
`StableRangeTests.ElementaryGenerationClient.rank_one_pivot`: an invertible
rank-one matrix over a commutative ring already has a unit leading entry.
These two fixtures are test-only, not production results; other helpers in
those two clients are private. Separate applications of all three theorems use
local rings, the nonlocal product of fields and finite Boolean indices. The
independent boundary proofs do not rely on those applications.
Further clients apply determinant-one generation to a nonlocal product matrix
and its Boolean reindexing, and check the stable quotient on nonidentity units.
`tests/StableRangeTests/SemilocalClient.lean` also establishes finite maximal
spectrum for `ZMod 2 × ZMod 2` as the test-only public fixture
`StableRangeTests.SemilocalClient.finite_maximalSpectrum_product`, checks a
right-unimodular pair with neither entry a unit, and applies the semilocal
theorem to its shortening and to the existing stable quotient determinant
criterion. Its zero-ring and local-ring specializations use the same theorem.
No positive-dimensional product-of-local-rings example is
compiled here. The integer pair `(5, 2)` shows that `(S₁)` fails without the
finite-maximal-spectrum hypothesis.

The [corner client](tests/StableRangeTests/CornerClient.lean) instantiates the
theorem over `M₃(ZMod 4)` and `M₃(ℕ → ZMod 4)`, using a shared
[matrix-unit fixture](tests/StableRangeTests/CornerMatrixFixtures.lean).
Its idempotent is noncentral, and its ordered right-unimodular pair consists
of noncommuting corner nonunits. It checks both an existential correction from
`(S₁)` and an explicit corner unit that is not an ambient unit, as well as
`e = 0`, `e = 1` and zero-ring cases.

The [semisimple regression client](tests/StableRangeTests/SemisimpleClient.lean)
checks complementary nonunit matrix projections and a stable-range shortening.
Separately, it exhibits noncommuting matrix units through the public test-only
theorem `StableRangeTests.SemisimpleClient.matrix_units_noncommutative`,
not a production library result. The same client tests infinite and empty
products, zero-index boundaries, a power-series ring with nonnilpotent Jacobson
radical, and cancellation through opposite rings.

## Scope and conventions

- Unimodularity uses right coefficients: `∑ i, r i * s i = 1`. Stable reduction
  uses `r i - r₀ * t i`. The row-vector matrix map is **left-linear**, acting by
  multiplication by the matrix on the right; no commutativity is silently added.
- `(S_n)` is a property at an index, not a least-index assertion. `IsStableRange`
  records a supplied least index. The zero ring satisfies `(S_0)`; assertions of
  least index one require the stated nontrivial/local hypotheses. Zero-dimensional
  `(S_1)` includes nonreduced rings such as `ZMod 4`.
- `ℕ →₀ M` is the countable direct sum of copies of arbitrary `M`, not necessarily
  a free or countably generated module. The shift theorem includes
  `Module.End ℕ (ℕ →₀ ℤ)`.
- Matrix unit-regularity permits an empty finite index. Normalization is real
  division by the cardinality: it gives zero in the empty case. Normalized
  identity-one and the advertised positive-size bounds use nonempty indices.
  An empty repeated-block family is not claimed to give an injective map.
- Right-coefficient kernel-product splitting works over arbitrary rings,
  including empty rows and the zero ring; splitting alone does not imply a
  free kernel. With a free right kernel, rectangular completion is equivalent
  to right-unimodularity, without stable range, commutativity, nontriviality or
  a specified matrix size. The commutative free-kernel results separately use
  either a stable-range bound or a chosen row of a specified two-sided square
  inverse; the latter does not manufacture an index for an empty matrix.
- Finite-free cancellation uses an explicit presentation and a stable-range
  bound; no preliminary freeness or nontriviality hypothesis is needed.
  First-row completion preserves the original row, not only its equivalence
  class. Dimension-bound variants require a commutative noetherian ring.
- This is not a general Morita-invariance theorem, stable general-linear-group
  construction, arbitrary stably-free cancellation theorem, or K-theory library.
  These results do not establish formal coverage of a whole source book.

## Reproducible build

The exact environment is Lean `leanprover/lean4:v4.34.0-rc2`, Mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, and `general-linear-groups`
`2683f75e2c5774ddd1295c46062035cb6afabb8a`. `lake-manifest.json` pins the full
resolved graph. The official GLG GitHub repository is private and requires
authorized access; no credentials belong in this repository or its documentation.

Install the pinned `lean-toolchain` with elan and, from the repository root,
successfully fetch the matching Mathlib cache **before** building. The default
build runs both `StableRange` and `StableRangeTests` (including the
regression clients):

```sh
env LEAN_NUM_THREADS=2 lake exe cache get
env LEAN_NUM_THREADS=2 lake --wfail -KwarningAsError=true build
```

The cache fetch is also required after replacing `.lake` or changing pins;
`LEAN_NUM_THREADS=2` does not cap child-process memory. To rebuild just the
**project** while retaining the matching fetched dependency cache:

```sh
lake clean stable-range
time env LEAN_NUM_THREADS=2 lake --wfail -KwarningAsError=true build
```

Do not use unqualified `lake clean` here: it removes dependency outputs.

For the historical, source-bound native API and its limitations, see the
[API reference](docs/API.md), [manifest](docs/api-manifest.json) and
[generation guide](docs/README.md). The manifest describes an older snapshot,
not this checkout; its historical signatures and line ranges are not current
API documentation.

## References

- Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  August 29, 2013 complete-book build, Chapter I, §1: unimodular rows,
  the stable-range dimension bound, Theorem I.1.3 and Exercises I.1.5,
  I.1.12(v), I.1.13(a)–(f). These supply mathematical statements and
  context, not copied prose or an attribution of the library's independent
  proofs to the book.
- [Mathlib](https://github.com/leanprover-community/mathlib4) (pinned
  revision in `lakefile.toml`): prior formalizations of rings, ideals,
  local and semisimple rings, Krull dimension, flatness, modules, linear
  equivalences, matrix blocks, idempotent corners, and rank. The proofs
  use these definitions, theorems and constructions.
- `general-linear-groups` (pinned revision in `lakefile.toml`): prior
  formalizations of quasiregular two-sided ideals and their radical
  criterion, matrix corners and ordered block units, elementary subgroups,
  conditional unit-pivot induction, finite reindexing, the stable determinant
  and its rank-one quotient section. The elementary-generation results
  generalize its local statements using the stable-range hypothesis.

## License, credit and provenance

Original project contributions are offered under the Apache License 2.0 in
[LICENSE](LICENSE). Lean file credit is `Authors: Formal Frontier Agents`, a
collective attribution, **not** a claim that an unverified entity owns copyright.
Prism contributed the principal stable-range, regularity, dimension, rank,
cancellation and two-shear kernel work, together with the exact-coordinate
finite-free cancellation and first-row assembly designs. Distinct agents
proved finite-free peeling and the coordinate-first row/matrix completion
from the existing kernel API; other agents contributed the
semilocal, product, semisimple, opposite-ring, matrix/corner and elementary
generation results, the invertible-matrix-row kernel construction and
distinct prefix-ideal fixture and production work. The
[documentation credits](docs/CREDITS.md) distinguish their work and the
original API adapter and notes from later documentation fixes.

Formal Frontier Agents are AI agents. AI assistance was used in research, Lean
proof development, clients, documentation and maintenance. Attribution, a build
or an Apache notice alone does not establish ownership or lawful redistribution
of third-party expression.

Weibel's *K-book* supplies published mathematical results as well as
motivation; the dimension bound and exercise-level statements are credited
in the relevant theorem docstrings. The finite-prime/height dimension
argument does not claim to reproduce the cited Bass V.3.5 proof.
Mathlib and `general-linear-groups` supply formalized interfaces and proof
ingredients as detailed in [References](#references); both are imported,
not vendored, and retain their respective licenses and attributions.

No source PDF, scan, substantial book quotation, generated API website or
other binary asset is shipped. The local Markdown API and adapter have
[separate provenance](docs/CREDITS.md). Source access grants no permission to
reproduce book assets; no human mathematical review, source-author endorsement
or unverified copyright holder is asserted.
