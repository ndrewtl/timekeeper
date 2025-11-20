namespace Timekeeper

abbrev Val := Nat

abbrev VariableName := String

inductive Variable
| logical : VariableName -> Variable
| program : VariableName -> Variable
deriving Repr, DecidableEq

abbrev Store := Variable -> Val

abbrev Event := List Val

-- A Trace contains both an event and a snapshot of the state when the event was
-- emitted. This is necessary to evaluate the specification functions under the
-- correct state at each step
structure TraceEntry where
  mk ::
  event : Event
  store : Store

abbrev Trace := List TraceEntry
