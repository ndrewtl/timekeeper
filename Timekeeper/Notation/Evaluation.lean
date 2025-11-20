import Timekeeper.Types

namespace Timekeeper.Notation
open Timekeeper

class Evaluation (α : Type) where
  β : Type
  eval : α -> Store -> Trace -> β

notation:330 "⟦ " E " ⟧(" σ ", " τ ")" => Evaluation.eval E σ τ
