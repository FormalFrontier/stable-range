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

/-!
# Public-import regression clients for stable range

The client modules use Mathlib's matrix, finite-ring, power-series and
maximal-spectrum formalizations for concrete examples. Finite-free cancellation
and first-row completion clients exercise fields, integers, independent module
universes, an empty stabilizer and the zero ring.
Square right-row clients exercise a supplied inverse column over the integers
and noncommutative integer matrices, including empty and unary boundaries.

## References

* Mathlib, for the algebraic fixtures exercised in the imported clients.
-/
