/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.Basic
public import StableRange.Quotient
public import StableRange.Local
public import StableRange.Semilocal
public import StableRange.Regular
public import StableRange.Corner
public import StableRange.Matrix
public import StableRange.Opposite
public import StableRange.Product
public import StableRange.Semisimple
public import StableRange.Commutative
public import StableRange.CommutativeStableRange
public import StableRange.BassDimension
public import StableRange.DivisionRing
public import StableRange.RepeatedBlock
public import StableRange.DivisionRingRank
public import StableRange.Cancellation
public import StableRange.RowKernel
public import StableRange.FiniteFree
public import StableRange.RowCompletion
public import StableRange.ElementaryGeneration
public import StableRange.DeterminantGeneration

/-!
# Bass stable range

Reusable definitions and results about finite right-unimodular rows, Bass
stable-range conditions, quotient invariance, local rings, direct finiteness,
regular rings, and finite matrix rings over division rings. Every commutative
ring with finite maximal spectrum satisfies `(S₁)`.
Finite square matrix rings over arbitrary rings satisfying `(S₁)` also satisfy
`(S₁)`, including empty index types.
Dependent products preserve stable-range conditions, and semisimple rings and
rings with semisimple Jacobson-radical quotients satisfy `(S₁)`.
The library also proves free-summand cancellation for modules whose
endomorphism rings satisfy stable range one.
Endomorphism rings of arbitrary vector spaces over division rings are von
Neumann-regular, whereas countable direct sums of copies of nonzero modules
have non-unit-regular endomorphism rings.
Commutative von Neumann-regular rings are exactly the reduced rings of Krull
dimension at most zero, and every module over such a ring is flat.
Every zero-dimensional commutative ring satisfies `(S₁)`, every nontrivial
such ring has least stable range one, and every commutative von
Neumann-regular ring is unit-regular.
More generally, a commutative noetherian ring of Krull dimension at most `d`
satisfies `(S_(d+1))`.
Over commutative rings, sufficiently long right-unimodular coefficient rows
have free kernels under the corresponding stable-range condition. Independently
of stable range, a row in a matrix with a specified two-sided inverse has kernel
equivalent to the function module on the complementary column indices.
An explicit finite stable presentation cancels a finite free summand when the
remaining coordinate count meets the stable-range bound, retaining the exact
coordinate count even over the zero ring. Under the same bound, a right-unimodular
row extends to an invertible matrix whose first row is the original row.
It provides row rank and normalized row rank for matrices over division rings,
including realization of every possible finite square-matrix row rank, scaling,
and normalized invariance under repeated diagonal blocks.
Repeated diagonal blocks of square matrices are also packaged as injective
ring homomorphisms for nonempty finite block families over arbitrary possibly
nonassociative and noncommutative `NonAssocSemiring` coefficients.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter I, §1 (stable range, finite stable presentations, row completion,
  unimodular rows and Exercises I.1.5,
  I.1.12–I.1.13).
* Mathlib, for the underlying ring, module, ideal, dimension and matrix APIs.
* `general-linear-groups`, for quasiregular ideals, elementary matrices and
  stable determinant constructions.
-/
