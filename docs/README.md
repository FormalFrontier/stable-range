# Mathematical API and historical native displays

The [headline results](../README.md#headline-results) cover Bass stable range,
regularity, division-ring ranks, commutative dimension bounds, cancellation
and free coefficient-row kernels. [API.md](API.md) records historical native
visible signatures and source docstrings for **121 display sites** across the
twelve mathematical `StableRange.*` leaves.
There are **23** supplementary explanations labeled *API note (not a source
docstring)*. The aggregate `StableRange` and `PublicAPIClient` each have an
explicit zero-site record. The latter is a private regression client, not a
library export; its 65 named private theorems do not become native public
displays. All fourteen module records, including the two empty records, are
source-bound in [api-manifest.json](api-manifest.json).

Native public display selection is not an ordinary-import ownership inventory
and not a full private/generated/raw kernel declaration census. The 121 visible
sites correspond to the 134 named mathematical commands excluding 13 private
helpers; the 65 named private clients are outside both counts. Additional
compiler-generated names may exist. The historical selected 199-name axiom
check covers 134 named commands plus 65 private clients, *not* all raw and
generated declarations. A separately recorded native build and complete
transitive standard-axiom audit covered the accepted original release; this
fixed Markdown is not itself proof evidence, independent semantic review or a
rights verdict.

## Mathematical orientation

- `Bass.IsRightUnimodular` uses **right coefficient witnesses** even for
  noncommutative rings. `StableRangeCondition R n` means `(S_n)`, whereas
  `IsStableRange R n` additionally states that `n` is least. The zero ring can
  satisfy `(S_0)`; the `S₁` and least-index-one results have different premises.
- The countable-sum counterexample uses `ℕ →₀ M` for **any nonzero module**,
  not a free-module hypothesis. Product cancellation assumes `(S₁)` for
  `Module.End R M`, not that `M` is finite or projective.
- `Matrix.rowRank` is the finrank of the range of a **left-linear** row-vector
  map defined by **multiplication on the right**. Matrix unit regularity and
  row rank admit empty finite indices. Positive-size normalized-rank claims
  and repeated-block injectivity explicitly require nonempty index types.
- `Matrix.repeatBlockHom` has `NonAssocSemiring` coefficients. Zero-dimensional
  commutative `(S₁)` needs neither reducedness nor nontriviality; the least
  range-one result does require `Nontrivial`. The dimension-`d` bound needs
  `CommRing`, `IsNoetherianRing`, and `Ring.KrullDimLE d`.
- The commutative stable-range row-kernel equivalence needs a right-unimodular
  row of the stated length. The separate inverse-matrix kernel equivalence
  instead requires a chosen row `i : Fin n` and **both** inverse identities;
  it has no stable-range hypothesis. No index `i` exists when `n = 0`.

The [root README](../README.md) supplies public-import and compiled examples;
the full [API](API.md) supplies literal native signatures, including implicit
arguments. Native rendering can suppress inferable types or abbreviate
notations; the linked Lean source remains authoritative. Relative source links
do not rely on an unpublished GitHub revision.

## Optional historical native reproduction

The [committed manifest](api-manifest.json) describes a particular **original
source snapshot**, original metadata and original native SQLite/doc-gen4 data.
It is not a manifest for this checkout's changed README, YAML, docs index or
SPDX-only Lean headers. Those changed inputs invalidate both its Git-object
and committed-hash `--check` comparisons; do not update a hash merely to
silence drift. The genuine original source revision, native records and SQLite
database are retained in private task/issue evidence, **not supplied by the
official published history or this repository**. Without those prerequisites,
the following is an optional historical recipe, not a current-checkout
`--check` pass claim or a request to regenerate documentation for this cleanup.

Keep a separate **unchanged core-only** `leanprover/doc-gen4` checkout at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, tree
`ebf77f3e174c145c9ca2db0df1c18a78ae87c93b`, committed tool manifest,
and Lean `v4.34.0-rc2`. Build the native tool there with `lake build doc-gen4`;
it is not installed as a dependency of this library. A C compiler (`cc`) must
be in that build's `PATH`. In this repository, use the pinned toolchain and
**first successfully fetch the matching mathlib cache**, even in a new or
replaced `.lake`, then build both default targets:

```sh
env LEAN_NUM_THREADS=2 lake exe cache get
env LEAN_NUM_THREADS=2 lake --wfail -KwarningAsError=true build
```

Run these commands only in a checkout of the manifest's **original source**
with genuine matching native data and SQLite database. On unchanged inputs,
the final `--check` reports `matched` only when source, pins, native records,
SQLite database and generated documentation all agree. It refuses changed
source, pin or documentation bytes. Here that check would rightly refuse;
synthetic tests do not authenticate native regeneration.
Set the executable to the native build's absolute path. The source-linker
argument is a neutral `source-snapshot/<fullcommit>/<path>` identifier, not a
GitHub URL or an end-range suffix. The native SQLite database supplies the
start and end lines, which the adapter checks against the actual local source.
Create the fresh SQLite parent *before* invoking `single`:

```sh
docgen_executable=/absolute/path/to/doc-gen4
docs_work=$(mktemp -d)
mkdir "$docs_work/analysis" "$docs_work/rendered"
source_revision=$(python3 -c 'import json; print(json.load(open("docs/api-manifest.json"))["analyzed_source_revision"])')
for leaf in Basic Quotient Local Regular Commutative CommutativeStableRange BassDimension DivisionRing RepeatedBlock DivisionRingRank Cancellation RowKernel; do
  lake env "$docgen_executable" single --build "$docs_work/analysis" "StableRange.$leaf" api.db "source-snapshot/$source_revision/StableRange/$leaf.lean"
done
lake env "$docgen_executable" single --build "$docs_work/analysis" StableRange api.db "source-snapshot/$source_revision/StableRange.lean"
lake env "$docgen_executable" single --build "$docs_work/analysis" PublicAPIClient api.db "source-snapshot/$source_revision/tests/PublicAPIClient.lean"
lake env "$docgen_executable" bibPrepass --build "$docs_work/rendered" --none
lake env "$docgen_executable" fromDb --build "$docs_work/rendered" --manifest "$docs_work/rendered/manifest.json" "$docs_work/analysis/api.db"
python3 -B scripts/generate_api.py --native-data "$docs_work/rendered/doc-data" --native-db "$docs_work/analysis/api.db" --source-revision "$source_revision" --check
python3 -B scripts/test_generate_api.py
```

The wrapper preserves every visible signature token; it normalizes header
whitespace only, validates names/kinds/modules/signatures and normalized native
docstrings against the fixed inventory, and refuses missing modules, incorrect
source-snapshot identifiers, source ranges, sources/pins/metadata and output
drift. The exact per-name module/position/start/end map is in the fixed
inventory. For these neutral identifiers doc-gen4 emits no end-range suffix:
the unchanged native SQLite database instead supplies full ranges. The
normal Git-object mode requires `--native-db`, checking every displayed
name/range/JSON start join and the fourteen additional module-documentation
ranges, then the exact database SHA-256 and source bounds. Source-only mode
uses the committed map and manifest's matching database/source/native-record
hash commitments; it may also verify the DB when supplied. `--check`
compares the complete generated files and canonical native module records to
the manifest without writing. The data-only test constructs synthetic header
markup; it **does not authenticate native generation**. The actual fourteen
original native records and command output are retained separately in private
task evidence. Rebuilds with a new source revision need a newly inspected
inventory and source-bound manifest; never replace a hash to silence drift.

Where the analyzed Git commit is present, the adapter compares **all fourteen
Lean sources**, the toolchain, Lake configuration/manifest, and root metadata
against exact Git objects. For source-only trees or Git's explicit `missing`
result, it instead requires the original manifest's identical source hashes,
source commit/tree, tool selection and module/path map. Broken Git or a
non-commit object fails closed. The manifest binds its original README/docs
inputs separately and cannot certify this changed checkout.

GLG `1f8fd3e39080be39586ea22fa56c157167eefd00` is the official pinned
dependency, not vendored code. Uppercase Lean `-T0` disables the allocation
timeout; it is **not** trust-zero or a separate stored-proof check. No
source-wide coverage decision follows from these API displays.
