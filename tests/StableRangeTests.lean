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

/-!
# Public-import regression clients for stable range

The client modules use Mathlib's matrix, finite-ring, power-series and
maximal-spectrum formalizations for concrete examples. Finite-free cancellation
and first-row completion clients exercise fields, integers, independent module
universes, an empty stabilizer and the zero ring.

## References

* Mathlib, for the algebraic fixtures exercised in the imported clients.
-/
