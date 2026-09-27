# stable-range

Reusable Lean theory of Bass stable range, unimodular rows, and applications.

The initial development defines finite right-unimodular rows over arbitrary
possibly noncommutative rings, Bass's conditions `(S_n)`, and relational least
stable range. It develops monotonicity, descent along surjective ring
homomorphisms, invariance under quotients by quasi-regular two-sided ideals,
the stable-range-one theorem for local rings, direct finiteness under
`(S_1)`, and the equivalence between unit-regularity and `(S_1)` for von
Neumann-regular rings. For regular rings it constructs explicit complementary
principal right ideals from inner inverses. Stable-range conditions are
invariant under ring equivalence, and a module whose endomorphism ring has
`(S_1)` cancels from binary direct products without finiteness or projectivity
assumptions. Consequently, finite powers of the regular right module over a
unit-regular ring cannot absorb a nontrivial complementary module. It also
proves that endomorphism rings of arbitrary vector spaces over division rings
are von Neumann-regular, while the endomorphism ring of a countable direct sum
of copies of any nonzero module is not unit-regular. In finite dimension,
endomorphisms have automorphic inner inverses, and consequently finite square
matrix rings over division rings are unit-regular. It also develops row rank for
rectangular matrices over division rings and the normalized real-valued row rank
of nonempty finite square matrices, including multiplication bounds and
additivity on orthogonal idempotents. Row rank is invariant under independent
equivalences of the row and column index types, and normalized row rank is
invariant under simultaneous reindexing. Every natural-number row rank up to
the size of a finite square matrix is realized, with the corresponding
normalized value. Repeating a rectangular matrix on finitely many diagonal
blocks scales its row rank by the number of blocks; for nonempty square
matrices and a nonempty block family, normalized row rank is unchanged. Over
arbitrary possibly nonassociative and noncommutative
`NonAssocSemiring` coefficients, repeating square matrices on finitely many
diagonal blocks is a ring homomorphism, injective when the block family is
nonempty.

For commutative rings, von Neumann regularity is equivalent to reducedness
together with Krull dimension at most zero. Every module over such a ring is
flat, with no finite-generation or Noetherian hypothesis. Every commutative
ring of Krull dimension at most zero satisfies `(S₁)` (and has least stable
range one when nontrivial), without a reducedness assumption. Every
commutative von Neumann-regular ring is unit-regular.

More generally, every commutative noetherian ring of Krull dimension at most
`d` satisfies Bass's condition `(S_(d+1))`. The proof uses a finite-antichain
prime-avoidance construction and minimal-prime height induction. It does not
assume reducedness, nontriviality, decidable equality, infinite residue fields,
or a chosen presentation of the ring.

For commutative rings satisfying `(S_s)`, every right-unimodular coefficient
row of length at least `s + 1` has a free kernel. The proof is an explicit
two-shear reduction to the split kernel of the shortened unimodular row; it
does not assume Noetherianity, a dimension bound, or nontriviality.
Independently of stable range, any row of a square matrix with a specified
two-sided inverse has free coefficient kernel, via an explicit equivalence with
the function module on the complementary column indices.

This repository is organized around source-independent algebra.
Interpretation, provenance, correspondence, and coverage for motivating
sources remain in their source-metadata repositories. Prism is responsible for
the initial integration on behalf of the Source-maintainers team.

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
  No source-wide formalization or release certification follows from these APIs.

## Reproducible build

The exact environment is Lean `leanprover/lean4:v4.34.0-rc2`, Mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103`, and `general-linear-groups`
`1f8fd3e39080be39586ea22fa56c157167eefd00`. `lake-manifest.json` pins the full
resolved graph. The official GLG GitHub repository is private and requires
authorized access; no credentials belong in this repository or its documentation.

Install the toolchain named in `lean-toolchain` through elan, then run from the
repository root:

```sh
env LEAN_NUM_THREADS=2 lake exe cache get
env LEAN_NUM_THREADS=2 lake --wfail -KwarningAsError=true build
env LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true tests/PublicAPIClient.lean
```

The matching cache fetch must succeed before building, including in a new
checkout or after replacing `.lake` or changing pins. The literal default builds
both `StableRange` and `StableRangeTests`. To reproduce a clean **project** build
while retaining the fetched dependencies:

```sh
lake clean stable-range
time env LEAN_NUM_THREADS=2 lake --wfail -KwarningAsError=true build
```

Do not run unqualified `lake clean` here: it also removes dependency outputs.
The author evidence and measured baseline are recorded in
internal readiness issue #38.
On 2026-09-25, the author's Linux container (23 GiB memory limit,
`LEAN_NUM_THREADS=2`, matching dependency cache retained) rebuilt all fourteen
project modules in the default graph successfully: 2,259 jobs, 17.448 seconds
wall time, 30.421 seconds user and 8.719 seconds system. This is one measured
clean-project/warm-dependency run, not a cold-cache or portable performance promise.
Ordinary source replay, including uppercase `-T0` (allocation timeout disabled),
is neither a trust-zero check nor a complete transitive axiom audit. Release
computational prerequisites are an applicable successful pinned build and a
complete transitive standard-axiom audit including private declarations; exact-input
evidence may be reused. Separate stored-proof replay, fresh expensive docgen and
repeated consumer builds are not release prerequisites.

The GLG pin above is the actual initial parentless official private GitHub root,
tree `b220afb712444f8b37435b5878231b0a41d525a8`, promoted and mirrored on
2026-09-26 after internal acceptance. This exact upstream dependency pin does
not imply a Stable Range release or a public Stable Range source commit.
On 2026-09-26, the previous source's author completed a raw stored-body inventory
(316 raw occurrences across fourteen targets; 37 codegen-only names separate)
and separate checks recorded in internal issue #38.
These author checks do not replace independent generated-API, metadata, semantic,
rights or whole-artifact review, or protected-promotion/consumer checks.
At the 2026-09-26 author handoff, the root `formalization.yaml` incorporated
metadata from then-unaccepted PR #40 and readiness changes from then-unaccepted
PR #39. Their inclusion was not acceptance; later verdicts attach to their
exact revisions. The metadata's `author-verified` status describes historical
author evidence, not a current independent-review or release verdict. The root
LICENSE is present and headers carry collective author credit, not established
ownership or independent rights clearance. The
genuine native generation and data-only tests are bounded documentation evidence,
not release acceptance or a whole-proof audit; see [generation limitations](docs/README.md).
The [API manifest](docs/api-manifest.json) binds a committed source snapshot,
native generation and documentation bytes. Its author checks are not an
independent review of this successor or a claim that the source snapshot is
available on GitHub.

## License, credit and provenance

Original project contributions are offered under the Apache License 2.0 in
[LICENSE](LICENSE). Lean file credit is `Authors: Formal Frontier Agents`, a
collective attribution, **not** a claim that an unverified entity owns copyright.
Prism authored the initial library and most subsequent developments. The
invertible-matrix-row kernel extension was contributed by
`formalization-worker-b`, Hive Task
`hive-request-905eb56085b0b843c8a3566340579c394a244d0b`, UID
`11244f44-2a43-49e1-96c4-1d9e06d57485`, commit
`84e27e284813f13af149284a4cf44a079f313f9a` (PR #37).
The isolated prefix-ideal recursor fixture was authored by worker-a Task
`hive-request-de3a7ada8b39474d68eb2f423d722fe442d5828d`, UID
`71af888b-804a-49e5-a144-911d4255f078`; the separate production replacement
and author checks were authored by worker-a Task
`hive-request-383df0a15b139fdb710024bff6a46b0e39e81849`, UID
`7489031a-54cc-43f5-9bd2-ba749058f328`. Neither Task independently
reviews or accepts its own work.
Git history and exact-candidate review records retain individual contributions,
corrections and reviewers; a historical approval alone does not transfer to a
later revision.

Formal Frontier Agents are AI agents. AI assistance was used in research, Lean
proof development, clients, documentation and maintenance. Attribution, a build,
or an Apache notice alone does not establish lawful redistribution of third-party
expression. The complete author-side current-file origin/notice packet and
independent clearance scope were recorded in issue #38. The proposed
truthful-header departure from Mathlib's copyright-format lint is not a
rights waiver; any release needs its applicable independent disposition.

Mathematical motivation includes Charles A. Weibel, *The K-book: An Introduction
to Algebraic K-theory*, August 29, 2013 complete-book build, especially Chapter I
Exercises 1.12–1.13 and the Bass stable-range/cancellation discussion. The source
repository retains exact interpretation, exposition and correspondence records;
the library does not require those records to state or use its results. The
project's direct Bass-dimension proof does not certify an unavailable cited book
or import its prose as a proof.

| Expression or formal dependency | Origin and treatment |
| --- | --- |
| Basic/quotient/local and commutative-regular development | Project-authored formal proofs related to retained Prism diagnostics in `source-weibel-k-book` at `a87ba2318d7e1c5e9d2f4f8784b6d4bc54588dba` and `c14b695a059e3c6888a2d1c9e4897aeb4a026df0`; naming, interfaces and native assumptions were generalized. Retention dates do not establish cross-repository precedence. |
| Remaining algebra/rank/cancellation/Bass proof | Project Lean constructions using native Mathlib APIs. `RepeatedBlock` was extracted from the earlier project rank module; it is not an independently sourced proof. |
| Invertible-row kernel extension | The PR #37 contribution above specializes native `LinearMap.iInfKerProjEquiv` and composes project kernel transport; no source-only candidate is a dependency. |
| Prefix-ideal recursor | The isolated fixture and the separate production replacement have distinct worker-a Task authors identified above; the production body uses `Nat.rec` while retaining the original public type and both definitional equations. |
| Mathlib and resolved support packages | Imported pinned dependencies, not vendored in this tree. Preserve their own licenses/attributions if separately redistributed; this project's LICENSE does not replace them. |
| GLG quasi-regular ideals | Imported pinned `GeneralLinearGroups.QuasiregularIdeal`; source-independent predicate and unit characterization, with its own project provenance. |
| License text | Unmodified official Apache 2.0 text from `https://www.apache.org/licenses/LICENSE-2.0.txt`; its appendix is a template, not an assertion of this project's holder. |

No source PDF, scan, substantial book quotation, vendored dependency, generated
API website or other binary asset is shipped in this tree. The local generated
Markdown API and its adapter have separate provenance in `docs/CREDITS.md`;
at the 2026-09-26 documentation-preparation checkpoint, independent review and
redistribution clearance of those artifacts had not been established; neither
is inherited from the mathematical source. Canonical source access is not a
redistribution grant. Additional artifacts, notices and the history actually
proposed for publication require their own inventory and clearance. This
successor's author-side provenance does not decide those later reviews.
