/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import StableRangeTests.PublicAPIClient
import StableRangeTests.MatrixClient
import StableRangeTests.CornerClient
import StableRangeTests.ElementaryGenerationClient
import StableRangeTests.SemilocalClient
import StableRangeTests.LocalJacobsonClient
import StableRangeTests.LocalIdealCommRingClient
import StableRangeTests.ProductMaximalIdealClient
import StableRangeTests.DivisionSemiringClient
import StableRangeTests.SemisimpleClient
import StableRangeTests.MatrixReflectionClient
import StableRangeTests.FiniteFreeClient
import StableRangeTests.RowCompletionClient
import StableRangeTests.RowCompletionTwoFixtures
import StableRangeTests.RowCompletionTwoClient
import StableRangeTests.RightCoefficientClient
import StableRangeTests.RightRowCompletionFixtures
import StableRangeTests.RightRowCompletionClient
import StableRangeTests.SquareRightRowCompletionFixtures
import StableRangeTests.SquareRightRowCompletionClient
import StableRangeTests.SquareRightRowCompletionCriterionClient
import StableRangeTests.CountableEndomorphismClient
import StableRangeTests.Module.SplitSurjective
import StableRangeTests.Module.SplitSurjectiveCompatibility

/-!
# Public-import regression clients for stable range

The client modules use Mathlib's matrix, finite-ring, power-series and
maximal-spectrum formalizations for concrete examples. Finite-free cancellation
and first-row completion clients exercise fields, integers, independent module
universes, an empty stabilizer and the zero ring.
Square right-row clients exercise a supplied inverse column over the integers
and noncommutative integer matrices, including empty and unary boundaries.
Local Jacobson-radical clients exercise division rings, noncommutative quaternion
dual numbers, commutative maximal-ideal agreement and nonlocal product boundaries.
Maximal-left-ideal clients compare the canonical radical with Mathlib's commutative
maximal ideal and distinguish the two maximal projection kernels of a nonlocal
product of quaternion division rings.
Division-semiring clients exercise the nonnegative reals, noncommutative real
quaternions, and the additive views of nonunits and maximal ideals.
Natural-scalar split-kernel clients reconstruct integer pairs and distinguish
horizontal and diagonal sections of the same projection.
Ring-scalar compatibility clients check kernel/image reconstruction and equal
specified sections through the deprecated public interfaces.

## References

* Mathlib, for the algebraic fixtures exercised in the imported clients.
-/
