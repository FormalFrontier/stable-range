# Mathematical API and historical native displays

The [headline results](../README.md#headline-results) describe the current
library. [API.md](API.md) instead records **historical** doc-gen4 visible
signatures and source docstrings for 121 sites across twelve mathematical
`StableRange.*` leaves. Its 23 supplementary explanations are labeled *API
note (not a source docstring)*. The aggregate root and the original
`PublicAPIClient` each have a zero-site record in the frozen
[manifest](api-manifest.json). The display selection is not an inventory of
ordinary imports, private/generated declarations or proof axioms.

The displayed client was a private regression client in that snapshot. Today's
relocated `tests/StableRangeTests/PublicAPIClient.lean` has private regression
proofs **and a public zero-ring fixture**, `zero_ring_condition`, which is not
a production-library result or imported by `StableRange`.

## Mathematical orientation

- `Bass.IsRightUnimodular` uses **right coefficient witnesses** even for
  noncommutative rings. `StableRangeCondition R n` means `(S_n)`, whereas
  `IsStableRange R n` additionally states that `n` is least. The zero ring can
  satisfy `(S_0)`; the `(S_1)` and least-index-one results have different premises.
- The countable-sum counterexample uses `ℕ →₀ M` for **any nonzero module**,
  not a free-module hypothesis. Product cancellation assumes `(S_1)` for
  `Module.End R M`, not that `M` is finite or projective.
- `Matrix.rowRank` is the finrank of the range of a **left-linear** row-vector
  map defined by **multiplication on the right**. Matrix unit regularity and
  row rank admit empty finite indices. Positive-size normalized-rank claims
  and repeated-block injectivity explicitly require nonempty index types.
- `Matrix.repeatBlockHom` has `NonAssocSemiring` coefficients. Zero-dimensional
  commutative `(S_1)` needs neither reducedness nor nontriviality; the least
  range-one result does require `Nontrivial`. The dimension-`d` bound needs
  `CommRing`, `IsNoetherianRing`, and `Ring.KrullDimLE d`.
- The commutative stable-range row-kernel equivalence needs a right-unimodular
  row of the stated length. The separate inverse-matrix kernel equivalence
  instead requires a chosen row `i : Fin n` and **both** inverse identities;
  it has no stable-range hypothesis. No index `i` exists when `n = 0`.

The [root README](../README.md) gives current public-import examples. The
frozen API reference is **not a current signature or line-number index**:
its `Matrix.rowRank_mul_le_left` display still includes an explicit
`DecidableEq n` parameter removed from the current theorem, and some original
source ranges no longer locate their declarations in today's files. Follow
the relative links only to navigate to a Lean filename, then check its actual
current declarations and positions. The old
`general-linear-groups` revision `1f8fd3e39080be39586ea22fa56c157167eefd00`
belongs to the earlier dependency graph; the current released dependency is
`4911287aa3c1a7e9f2acb81249766f2682da58fb`, with Mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`.

## Building and historical reproduction

The current library uses the toolchain and pins in `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json`. Fetch the matching Mathlib cache
before building both default targets, including the regression client:

```sh
env LEAN_NUM_THREADS=2 lake exe cache get
env LEAN_NUM_THREADS=2 lake --wfail -KwarningAsError=true build
```

The frozen manifest binds an **original source revision**, source ranges,
metadata, original native records and a native SQLite database. It cannot
validate the changed source and documentation in this checkout. Exact native
reproduction requires that original source, matching doc-gen4 tool and
genuine native records and database; those native data are not shipped here.
The historical hashes must not be changed to hide drift. The lightweight
`scripts/test_generate_api.py` uses synthetic markup and checks adapter
behavior, **not** native provenance or the current API. No historical
`--check` success or current-documentation regeneration is claimed.
