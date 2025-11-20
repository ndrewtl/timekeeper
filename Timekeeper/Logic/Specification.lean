import Timekeeper.Types
import Timekeeper.Logic.Assertion.TraceAssertion

namespace Timekeeper

abbrev Specification := Event -> TraceAssertion
namespace Specification

-- A specification function is well-formed iff it always returns well-formed
-- Trace Assertion
def wellFormed (S : Specification) : Prop :=
  ∀ e, (S e).wellFormed
