# stable-range

Reusable Lean theory of Bass stable range, unimodular rows, and applications.

The mathematical API is source-independent; interpretation and coverage of
motivating sources live in their source repositories. Import `StableRange` for
the complete library, or import individual leaves below.

## Headline results

These results build on Mathlib's algebraic APIs. The quasiregular-ideal
predicate and unit characterization are imported from the pinned
`general-linear-groups` dependency; the stable-range consequences are proved
here. Each link points to a declaration in this repository.

### Bass conditions, quotients and local rings

For arbitrary possibly noncommutative rings, the library defines finite
[right-unimodular rows](StableRange/Basic.lean#L32),
[Bass's `(S_n)` condition](StableRange/Basic.lean#L56), and
[relational least stable range](StableRange/Basic.lean#L154). It proves
[monotonicity](StableRange/Basic.lean#L143), invariance under ring equivalence,
[descent along surjective homomorphisms](StableRange/Quotient.lean#L55), and
[equivalence under quotients by quasiregular two-sided ideals](StableRange/Quotient.lean#L127).
[Nontrivial local rings have least stable range one](StableRange/Local.lean#L123).
The zero ring can satisfy `(S_0)`; this is not a least-index-one assertion.
Witnesses multiply on the right, and reduction order matters outside
commutative rings; see [Scope and conventions](#scope-and-conventions).

### Regular rings and module cancellation

`(S_1)` implies [direct finiteness](StableRange/Regular.lean#L38), and
under von Neumann regularity it is
[equivalent to unit-regularity](StableRange/Regular.lean#L331).
An inner inverse constructs
[complementary principal right ideals](StableRange/Regular.lean#L155).
If the endomorphism ring of a module `M` satisfies `(S_1)`, then
[`M` cancels from binary direct products](StableRange/Cancellation.lean#L35):
`M × A ≃ M × B` implies `A ≃ B`, without finiteness or projectivity
assumptions. For the regular right module, the statement uses the **opposite
ring**. [Finite powers](StableRange/Cancellation.lean#L184) over a unit-regular
ring cannot absorb a nontrivial complementary module.

### Endomorphisms and matrices over division rings

Endomorphisms of arbitrary vector spaces over division rings have
[inner inverses](StableRange/DivisionRing.lean#L37), hence von Neumann-regular
endomorphism rings. In finite dimension the inner inverse can be
[an automorphism](StableRange/DivisionRing.lean#L79), yielding
[unit-regular finite square matrix rings](StableRange/DivisionRing.lean#L124),
including empty indices. By contrast, the endomorphism ring of a countable
direct sum of copies of [any nonzero additive module](StableRange/Regular.lean#L255)
is not unit-regular; the sum need not be a free module.

### Row rank and repeated diagonal blocks

For division-ring coefficients, [row rank](StableRange/DivisionRingRank.lean#L42)
is the finrank of the image of the **left-linear row-vector map given by
right multiplication**. Rectangular ranks have multiplication bounds,
orthogonal-idempotent additivity and independent row/column reindexing.
For square matrices, [normalized rank](StableRange/DivisionRingRank.lean#L329)
is real row rank divided by index cardinality; identity rank one and positive
bounds require a nonempty index. Every allowed
[natural rank](StableRange/DivisionRingRank.lean#L151) and
[normalized value](StableRange/DivisionRingRank.lean#L334) is realized.
[Rectangular repeated blocks](StableRange/DivisionRingRank.lean#L319) scale
rank by the block count; normalized square rank is
[unchanged](StableRange/DivisionRingRank.lean#L412) for nonempty matrix and
block indices. Empty square matrices have normalized rank zero.

Separately, over arbitrary potentially nonassociative/noncommutative
`NonAssocSemiring` coefficients, [`Matrix.repeatBlockHom`](StableRange/RepeatedBlock.lean#L52)
is a ring homomorphism, [injective](StableRange/RepeatedBlock.lean#L70)
when the block family is nonempty.

### Commutative regularity and dimension bounds

A commutative ring is von Neumann regular
[iff it is reduced and has Krull dimension at most zero](StableRange/Commutative.lean#L103).
[All its modules are flat](StableRange/Commutative.lean#L132), with no finite or
Noetherian hypothesis. A commutative ring of dimension at most zero
[satisfies `(S_1)`](StableRange/CommutativeStableRange.lean#L102) even without
reducedness or nontriviality; *least* stable index one requires `Nontrivial`.
Every commutative von Neumann-regular ring is unit-regular.

More generally, a commutative Noetherian ring with `Ring.KrullDimLE d`
[satisfies `(S_(d+1))`](StableRange/BassDimension.lean#L548), proved by finite
prime avoidance and minimal-prime height induction, without an infinite-residue-
fields premise.

### Free kernels of coefficient rows

Over a commutative ring satisfying `(S_s)`, a right-unimodular coefficient
row of length at least `s + 1`
[has a free kernel](StableRange/RowKernel.lean#L348), by explicit two-shear
reduction. Independently of stable range, a *chosen row* of a square matrix
with an actual two-sided inverse has
[an explicit free-kernel equivalence](StableRange/RowKernel.lean#L159) with the
function module on complementary column indices. Both inverse identities
and an actual row index are required, not a merely proposed inverse.

## Public interface and use

Use ordinary `import StableRange` for the complete interface, or import a leaf
below. The root publicly re-exports all twelve leaves. The tests are not imported
by the root and add no public library declarations.

| Module (under `StableRange`) | Representative interface |
| --- | --- |
| `Basic` | `Bass.IsRightUnimodular`, `StableRangeCondition`, `IsStableRange`; monotonicity and equivalence |
| `Quotient` | `stableRangeCondition_of_surjective`, `stableRangeCondition_quotient_iff` |
| `Local` | `stableRangeCondition_one_of_isLocalRing`, `stableRange_one_of_isLocalRing` |
| `Regular` | `IsVonNeumannRegular`, `IsUnitRegular`, complementary principal right ideals and shift counterexample |
| `DivisionRing` | `LinearMap.exists_innerInverse`, `exists_linearEquiv_innerInverse`, matrix unit-regularity |
| `RepeatedBlock` | `Matrix.repeatBlock`, `repeatBlockHom`, Kronecker formula and injectivity |
| `DivisionRingRank` | `Matrix.rowRank`, `normalizedRowRank`, reindexing, realization and repeated blocks |
| `Commutative` | regular iff reduced and dimension at most zero; arbitrary-module flatness |
| `CommutativeStableRange` | zero-dimensional stable range; commutative regular implies unit-regular |
| `BassDimension` | finite-prime avoidance, prefix-ideal height bounds, `stableRangeCondition_succ_of_krullDimLE` |
| `Cancellation` | `exists_linearEquiv_of_prod_of_end_stableRangeCondition_one` and finite-power consequences |
| `RowKernel` | coefficient functionals, `kernelEquivOfLinearEquiv`, split kernels and explicit free-kernel equivalences |

Names without an explicit namespace in the table are in `Bass`, except the
division-ring and matrix entries as indicated. The [generated API](docs/API.md)
shows all 121 native mathematical-leaf display sites, their complete visible
signatures and 23 labeled authored notes for missing source docstrings.
The [generation guide](docs/README.md) explains its scope and exact snapshot;
[documentation credits](docs/CREDITS.md) record the reused adapter expression.
The aggregate root and private regression client are included as zero-site
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

`tests/PublicAPIClient.lean` contains persistent private proofs through the same
ordinary root import. Its two extra Mathlib imports supply concrete `ZMod`
fixtures and the Artinian dimension instance, not another route to project API.
It covers every module family, independent universes, opposite division rings,
nonassociative repeated-block coefficients, zero/empty boundaries, and a
nonreduced ring. It is part of the default build.

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
- Coefficient-row kernel results here use commutative rings. The invertible-row
  construction takes an actual row index and a specified two-sided matrix
  inverse; it does not manufacture an index for an empty matrix.
- This is not a general Morita-invariance theorem, stable general-linear-group
  construction, arbitrary stably-free cancellation theorem, or K-theory library.
  These results do not establish formal coverage of a whole source book.

## Reproducible build

The exact environment is Lean `leanprover/lean4:v4.34.0-rc2`, Mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103`, and `general-linear-groups`
`1f8fd3e39080be39586ea22fa56c157167eefd00`. `lake-manifest.json` pins the full
resolved graph. The official GLG GitHub repository is private and requires
authorized access; no credentials belong in this repository or its documentation.

Install the pinned `lean-toolchain` with elan and, from the repository root,
successfully fetch the matching Mathlib cache **before** building. The default
build runs both `StableRange` and `StableRangeTests` (the private API client):

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

Do not use unqualified `lake clean` here: it removes dependency outputs. For
the historical, source-bound native API and its limitations, see the
[API reference](docs/API.md), [manifest](docs/api-manifest.json) and
[generation guide](docs/README.md). The manifest records its **original**
source and documentation hashes; this README, changed headers and metadata
have different bytes. An old manifest hash must not be replaced to conceal
that drift, and native `--check` is not a success claim for this checkout.

## License, credit and provenance

Original project contributions are offered under the Apache License 2.0 in
[LICENSE](LICENSE). Lean file credit is `Authors: Formal Frontier Agents`, a
collective attribution, **not** a claim that an unverified entity owns copyright.
Prism contributed the principal mathematics, source research and internal
adaptations. A distinct contributor developed the invertible-matrix-row
kernel extension; a separate isolated prefix-ideal recursor fixture is not
the later production recursor repair. The [documentation credits](docs/CREDITS.md)
distinguish the original API adapter and authored notes from later source-link
and lifecycle corrections. Git history and the private preservation record
retain exact contribution and review identities; pooled worker identifiers
are not individual names.

Formal Frontier Agents are AI agents. AI assistance was used in research, Lean
proof development, clients, documentation and maintenance. Attribution, a build
or an Apache notice alone does not establish ownership or lawful redistribution
of third-party expression.

Mathematical motivation includes Charles A. Weibel, *The K-book: An Introduction
to Algebraic K-theory*, August 29, 2013 complete-book build, especially Chapter I
Exercises 1.12–1.13 and the Bass stable-range/cancellation discussion. The source
repository retains exact interpretation, exposition and correspondence records;
the library does not require those records to state or use its results. The
project's direct Bass-dimension proof does not certify an unavailable cited book
or import its prose as a proof.

| Expression or formal dependency | Origin and treatment |
| --- | --- |
| Basic/quotient/local and commutative-regular development | Project-authored formal proofs share expression with retained Prism diagnostics; names, interfaces and native assumptions were generalized. They are not wholly independent reinventions; retention dates do not establish precedence. |
| Remaining algebra/rank/cancellation/Bass proof | Project Lean constructions using native Mathlib APIs. `RepeatedBlock` was extracted from the earlier project rank module; it is not an independently sourced proof. |
| Invertible-row kernel extension | A distinct contributor specializes native `LinearMap.iInfKerProjEquiv` and composes project kernel transport; no source-only candidate is a dependency. |
| Prefix-ideal recursor | An isolated exact-type fixture and a separate production replacement have distinct contributors; the production body uses `Nat.rec` while retaining the original public type and both definitional equations. |
| Mathlib and resolved support packages | Imported pinned dependencies, not vendored in this tree. Preserve their own licenses/attributions if separately redistributed; this project's LICENSE does not replace them. |
| GLG quasi-regular ideals | Imported pinned `GeneralLinearGroups.QuasiregularIdeal`; source-independent predicate and unit characterization, with its own project provenance. |
| License text | Unmodified official Apache 2.0 text from `https://www.apache.org/licenses/LICENSE-2.0.txt`; its appendix is a template, not an assertion of this project's holder. |

No source PDF, scan, substantial book quotation, vendored dependency, generated
API website or other binary asset is shipped. The local generated Markdown API
and adapter have [separate provenance](docs/CREDITS.md). Source access grants
no permission to reproduce book assets; no human mathematical review,
source-author endorsement or unverified copyright holder is asserted.
