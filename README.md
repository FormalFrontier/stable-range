# stable-range

Reusable Lean theory of Bass stable range, unimodular rows, and applications.
The API is source-independent; import `StableRange` or individual leaves below.

## Headline results

These results use Mathlib. The quasiregular-ideal predicate and unit characterization
come from pinned `general-linear-groups`; the stable-range consequences are proved
here. The [guide](docs/GUIDE.md#headline-results) retains detailed statements,
coordinate formulas, compatibility names and client inventories.

- **[Bass conditions](StableRange/Basic.lean).** For arbitrary possibly noncommutative rings: right-unimodular
  rows, `(S_n)`, least stable index, monotonicity, ring-equivalence invariance and
  [surjective descent/quasiregular quotients](StableRange/Quotient.lean).
  [Nontrivial local rings](StableRange/Local.lean) have least stable range one.
- **Local interfaces.** [Division semirings](StableRange/Local.lean) are local with
  zero nonunits submonoid; the maximal-ideal additive comparison requires a
  commutative local semiring.
  For rings, locality is equivalent to Jacobson-radical maximality among all left
  ideals. In local rings the radical is the nonunits and contains every proper
  left ideal; these statements do not assume two-sidedness of the left ideals.
- **Preservation.** [Products](StableRange/Product.lean) preserve every `(S_n)`.
  [Semisimple rings and semisimple radical quotients](StableRange/Semisimple.lean)
  satisfy `(S₁)` without radical nilpotence. [Finite matrix rings](StableRange/Matrix.lean),
  [idempotent corners](StableRange/Corner.lean) and [opposites](StableRange/Opposite.lean)
  preserve `(S₁)`; matrix reflection needs nonempty indices, corners neither
  centrality nor fullness. [Commutative semilocal rings](StableRange/Semilocal.lean)
  satisfy `(S₁)` assuming only finite maximal spectrum, including the zero ring.
- **[Retract endomorphisms](StableRange/CategoryTheory/EndRetract.lean).**
  In any preadditive category, `i : X ⟶ Z`, `p : Z ⟶ X` and `i ≫ p = 𝟙 X`
  transfer `Bass.StableRangeCondition (End Z) 1` to
  `Bass.StableRangeCondition (End X) 1` for the original canonical endomorphism
  rings. Object and morphism universes are independent; no complementary object,
  finite-length or nonzero hypothesis is needed.
- **[Finite biproduct endomorphisms](StableRange/CategoryTheory/FiniteLocalEnd.lean).**
  In any preadditive category, a displayed finite biproduct of objects with local
  endomorphism rings, and every displayed retract of that biproduct, have canonical
  endomorphism rings satisfying `(S₁)`. Only that biproduct and, for the retract,
  its supplied retraction are required, with independent index universe; empty
  families and the zero biproduct are included. No vanishing of morphisms between
  summands is assumed.
- **Regularity and cancellation.** [`(S₁)`](StableRange/Regular.lean) implies direct
  finiteness, is equivalent to unit-valued pair shortening, and under von Neumann
  regularity is equivalent to unit-regularity.
  [Biproduct cancellation](StableRange/CategoryTheory/Cancellation.lean) in any
  preadditive category needs `(S₁)` for the canonical `End(X)` and only the two
  displayed biproducts. The remaining objects are unrestricted; local End is
  sufficient, and neither global sums nor commutativity is assumed.
  [Module cancellation](StableRange/Cancellation.lean) is a specialization,
  with independent carrier universes and no finiteness or projectivity;
  regular right modules use the opposite ring. [Division-ring vector-space endomorphisms](StableRange/DivisionRing.lean)
  have inner inverses; finite dimension gives automorphic inner inverses and
  unit-regular finite matrix rings, including empty indices.
- **Ranks and blocks.** [Division-ring row rank](StableRange/DivisionRingRank.lean)
  has rectangular bounds, reindexing, realization and repeated-block laws;
  normalized empty square rank is zero. [Repeated-block homomorphisms](StableRange/RepeatedBlock.lean)
  work over `NonAssocSemiring` coefficients, injectively for nonempty block families.
- **Commutative dimension bounds.** [Regularity](StableRange/Commutative.lean) is
  equivalent to reducedness and dimension at most zero; all modules over such
  regular rings are flat.
  [Dimension at most zero gives `(S₁)`](StableRange/CommutativeStableRange.lean)
  without reducedness or nontriviality; commutative regular rings are unit-regular.
  [Noetherian dimension at most `d` gives `(S_(d+1))`](StableRange/BassDimension.lean),
  with no infinite-residue-fields premise.
- **Specified splittings.** [A supplied linear right inverse of a linear map `f`](StableRange/Module/SplitSurjective.lean)
  gives `ker f × N ≃ₗ[R] M` over a semiring, for an additive commutative group `M`
  and additive commutative monoid `N`, in independent universes. [Right-unimodular
  coefficient rows](StableRange/RowKernel.lean) split over `Rᵐᵒᵖ` for any ring, including empty
  rows and the zero ring. Splitting alone does not give freeness.
- **Completion and IBN.** [Right-unimodularity and free right kernels](StableRange/RightRowCompletion.lean)
  characterize two-sided rectangular completion, preserving a supplied inverse
  column. For successor-length rows, [square completion](StableRange/SquareRightRowCompletionCriterion.lean)
  needs IBN only to infer kernel size; supplied matching coordinates and the
  converse need no IBN. The [countable endomorphism example](StableRange/CountableEndomorphism.lean)
  separates rectangular from square completion for nontrivial underlying modules,
  even for a unary row.
- **Commutative cancellation.** Under `(S_s)`, right-unimodular rows of length at
  least `s + 1` have free kernels. [Finite-free cancellation](StableRange/FiniteFree.lean) uses an
  explicit `P × R^m ≃ R^(n+m)` and `s ≤ n`, without prior freeness of `P`;
  [completion](StableRange/RowCompletion.lean) preserves the literal first row.
  Both allow zero rings; dimension-bound variants require Noetherianity.
  [Two-entry completion](StableRange/RowCompletionTwo.lean) retains supplied Bézout
  coefficients over commutative rings, with explicit scalar kernel coordinates.
- **Elementary matrices and determinants.** For commutative rings satisfying `(S₁)`,
  [elementary diagonalization](StableRange/ElementaryGeneration.lean) works in all
  finite ranks, including zero. [Determinant generation](StableRange/DeterminantGeneration.lean)
  identifies invertible determinant-one matrices with elementary matrices, the stable
  elementary subgroup with the determinant kernel, and its quotient with units,
  without locality, nontriviality or positive-rank hypotheses.

## Public interface and use

Add the library to your `lakefile.toml`:

```toml
[[require]]
name = "stable-range"
git = "https://github.com/FormalFrontier/stable-range.git"
rev = "main"
```

GitHub `main` contains reviewed releases.
Lake resolves `main` when the dependency is first added or updated;
`lake-manifest.json` locks that commit. To pin a release, use its full commit.
Libraries used together must share a compatible Mathlib revision and toolchain.
For the retract theorem, import `StableRange.CategoryTheory.EndRetract`.
For finite-biproduct endomorphisms, their arbitrary-retract corollary and the
module-theoretic supporting API, import `StableRange.CategoryTheory.FiniteLocalEnd`
explicitly; it also imports the retract theorem. The root import `StableRange`
does not re-export these leaves or the tests and their fixtures.

```lean
module
import StableRange

example (R : Type*) [CommRing R] [IsNoetherianRing R]
    (d : ℕ) [Ring.KrullDimLE d R] : Bass.StableRangeCondition R (d + 1) :=
  Bass.stableRangeCondition_succ_of_krullDimLE
```

The [guide](docs/GUIDE.md#public-interface-and-use) preserves the full example,
including the free-kernel application and detailed test-only client inventories.

## Modules

| Module (under `StableRange`) | Representative interface |
| --- | --- |
| `Basic` | `Bass.IsRightUnimodular`, `StableRangeCondition`, `IsStableRange`; monotonicity and equivalence |
| `Quotient` | `stableRangeCondition_of_surjective`, `stableRangeCondition_quotient_iff` |
| `Local` | `DivisionSemiring.isLocalRing`, `IsLocalRing.nonunitsAddSubmonoid_eq_bot`, `IsLocalRing.maximalIdeal_toAddSubmonoid`; `stableRangeCondition_one_of_isLocalRing`, `stableRange_one_of_isLocalRing`, `IsLocalRing.mem_ringJacobson_iff`, `IsLocalRing.le_ringJacobson`, `IsLocalRing.of_ringJacobson_isMaximal`, `IsLocalRing.iff_ringJacobson_isMaximal` |
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
| `CategoryTheory.Cancellation` | `CategoryTheory.nonempty_iso_of_biprod_iso_of_end_stableRangeCondition_one` and the local-End corollary, with only the two displayed sums |
| `CategoryTheory.EndCorner` | `CategoryTheory.endCornerRingEquivOfRetract` with extension and restriction formulas; `CategoryTheory.Limits.biproduct.endCornerRingEquiv` and finite orthogonal completeness |
| `CategoryTheory.EndRetract` | `CategoryTheory.stableRangeCondition_one_end_of_retract` for the original canonical endomorphism rings of any displayed retraction |
| `CategoryTheory.FiniteLocalEnd` | `CategoryTheory.stableRangeCondition_one_end_biproduct` and `CategoryTheory.stableRangeCondition_one_end_of_retract_biproduct` for any retract of the displayed finite local-End biproduct |
| `Module.LocalEnd` | projective modules with local endomorphism semirings; unique maximal submodules in the finitely generated case, and simple radical quotients over rings |
| `Module.Corner` | `IsIdempotentElem.cornerCongr`, `IsIdempotentElem.cornerOpEquiv`, `IsIdempotentElem.cornerEquivEnd` |
| `Module.Decomposition` | `CompleteOrthogonalIdempotents.linearEquivPiRange`, with projection coordinates and summation inverse |
| `Module.Radical` | `Module.jacobson_pi` for finite products of modules over arbitrary rings |
| `Module.SemisimpleQuotient` | `Ring.isSemisimpleRing_quotient_jacobson_of_linearEquiv_pi` for finite decompositions of the canonical left regular module |
| `Cancellation` | `exists_linearEquiv_of_prod_of_end_stableRangeCondition_one` and finite-power consequences |
| `Module.SplitSurjective` | `LinearMap.kerProdEquivOfRightInverse`, forward and inverse coordinates over semirings, and right-split-exact comparison |
| `RowKernel` | `kernelEquivOfLinearEquiv`, arbitrary-ring right-linear coefficient rows and split kernels; commutative free-kernel equivalences |
| `RightRowCompletion` | supplied right-linear kernel coordinates and two-sided rectangular inverse matrices; converse kernel equivalence and free-kernel criterion |
| `CountableEndomorphism` | even/odd coordinate splitting; non-IBN endomorphism ring and right-unimodular unary row with free nonzero kernel but no square completion |
| `SquareRightRowCompletion` | square `GL` construction preserving a supplied inverse column, with explicit actions and reverse free-kernel implication |
| `SquareRightRowCompletionCriterion` | free right-kernel iff square completion over IBN rings |
| `RowCompletionTwo` | supplied-witness `SL(2, R)` row completion, scalar kernel coordinates and supplied-product cancellation over commutative rings |
| `FiniteFree` | explicit finite-free summand cancellation and exact-size freeness under `(S_s)` or a noetherian dimension bound |
| `RowCompletion` | first-coordinate equivalence, completed matrix and two-sided inverse under `(S_s)` or a noetherian dimension bound |
| `ElementaryGeneration` | commutative `(S₁)` elementary unit pivots, diagonalization of `Fin n` matrices and finite reindexing |
| `DeterminantGeneration` | finite determinant-one membership, stable determinant kernel and quotient-to-units equivalence under commutative `(S₁)` |

Names without an explicit namespace in the table are in `Bass`, except the
division-ring, matrix and categorical entries as indicated. The local radical characteristic
and additive-object comparisons are in `IsLocalRing`; division-semiring locality
is in `DivisionSemiring`.

The [historical generated API](docs/API.md), [manifest](docs/api-manifest.json) and
[generation guide](docs/README.md) describe an older snapshot, not current signatures
or line ranges: 121 mathematical-leaf display sites, 23 authored notes and zero-site
root/client records. [Documentation credits](docs/CREDITS.md) record the adapter expression.

## Scope and conventions

Rows use right witnesses `∑ i, r i * s i = 1` and reduction `r i - r₀ * t i`.
Row-vector maps are left-linear, multiplying on the right; coefficient-row kernel
and completion maps are right-linear column actions over the opposite ring.
`(S_n)` is not a least-index assertion: the zero ring satisfies `(S_0)`;
least index one needs the stated nontrivial/local hypotheses. Normalized identity
rank one and positive bounds need nonempty indices. Splittings retain the supplied
section/Bézout coefficients; a chosen invertible-matrix row needs an actual index
and both inverse identities. Exact-size cancellation does not assert unique rank
for zero rings. See the [full conventions](docs/GUIDE.md#scope-and-conventions).
In the retract API, the category and additive data are unchanged, and endomorphism
multiplication is `a * b = b ≫ a`. For `i : X ⟶ Z`, `p : Z ⟶ X` and
`hip : i ≫ p = 𝟙 X`, put
`he := CategoryTheory.isIdempotentElem_comp_of_retract i p hip`.
The equivalence `CategoryTheory.endCornerRingEquivOfRetract` has codomain the
canonical `he.Corner`, with unit `p ≫ i`, not `𝟙 Z`.
`CategoryTheory.val_endCornerRingEquivOfRetract_apply` gives the forward value
`p ≫ a ≫ i`; `CategoryTheory.endCornerRingEquivOfRetract_symm_apply` gives
`i ≫ c.1 ≫ p` for `c : he.Corner`. Ambient compression `r ↦ i ≫ r ≫ p`
is not in general a ring homomorphism.

No general Morita invariance, general stably-free cancellation, stable general-linear-
group construction, free-object-to-`K₀` bridge, whole-book coverage or general-ring
determinant-one generation is claimed.

## Reproducible build

The exact environment is Lean `leanprover/lean4:v4.34.0-rc2`, Mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, and `general-linear-groups`
`2683f75e2c5774ddd1295c46062035cb6afabb8a`. `lake-manifest.json` pins the full
resolved graph. The pinned dependency is available from
the [General Linear Groups GitHub repository](https://github.com/FormalFrontier/general-linear-groups).

Install the pinned toolchain with elan and fetch the matching Mathlib cache first.
The default build includes `StableRange` and `StableRangeTests`:

```sh
env LEAN_NUM_THREADS=2 lake exe cache get
env LEAN_NUM_THREADS=2 lake --wfail -KwarningAsError=true build
```

The finite-biproduct leaf, which imports the retract theorem, is built separately:

```sh
env LEAN_NUM_THREADS=2 lake --wfail -KwarningAsError=true build +StableRange.CategoryTheory.FiniteLocalEnd
```

`LEAN_NUM_THREADS=2` does not cap child-process memory. The [build guide](docs/GUIDE.md#reproducible-build)
retains cache/rebuild details; unqualified `lake clean` removes dependency outputs.

## References

- Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  August 29, 2013 complete-book build, Chapter I, §§1–2: unimodular rows,
  the stable-range dimension bound, Theorem I.1.3 and Exercises I.1.5,
  I.1.12(v), I.1.13(a)–(f), and the local-ring discussion and radical
  identification used in Lemma I.2.2. These supply mathematical statements and
  context, not copied prose or an attribution of the library's independent
  proofs to the book.
- [Mathlib](https://github.com/leanprover-community/mathlib4) (pinned
  revision in `lakefile.toml`): prior formalizations of rings, ideals,
  local and semisimple rings, Jacobson radicals, dual numbers, quaternions,
  Krull dimension, flatness, modules, linear equivalences, matrix blocks,
  idempotent corners, rank, preadditive categories, biproducts and additive
  envelopes. Categorical cancellation reuses Kim Morrison's Gaussian elimination
  and matrix-category embedding. The local-semiring results generalize Mathlib's
  field-locality instance using its local-semiring constructor and the
  group-with-zero unit criterion. The additive comparisons use its nonunits,
  submonoid, submodule and maximal-ideal interfaces. The proofs use these
  definitions, theorems and constructions. Finite-biproduct endomorphisms further
  reuse its projective splitting, finite direct-sum decomposition, simple-module
  and module-radical quotient interfaces; the proof decomposes the canonical left
  regular module by right multiplication and identifies range endomorphisms with
  opposite corners.
- [Homological Algebra](https://github.com/FormalFrontier/homological-algebra),
  `HomologicalAlgebra.Preadditive.BiproductUniqueness`: the prior formalization
  approach for additive-envelope transport, canonical End ring comparison and
  fully faithful isomorphism reflection followed by categorical cancellation.
  This is credit for a formalization approach, not a package dependency.
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
finite-free cancellation and first-row assembly designs. The categorical
cancellation theorem generalizes that module proof using the existing
unit-shortening theorem and Mathlib's Gaussian elimination and additive envelope.
Its transport through the envelope, canonical End ring comparison and reflection
follow the earlier `HomologicalAlgebra.Preadditive.BiproductUniqueness`
formalization approach, separately from Mathlib's underlying implementations.
The original module theorem is recovered by universe-preserving specialization.
Distinct agents
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
