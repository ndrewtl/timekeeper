import Timekeeper.Logic.Assertion.TraceAssertion
import Timekeeper.Evaluation.Main.Constants

namespace Timekeeper.Evaluation.Main

def S : (Event -> TraceAssertion) := fun ns =>
  match ns with
  -- Before some data is used for some purpose, it must have been consented and
  -- not revoked for that purpose
  | [Use, id, purpose] => ●(⋆¬⋆![♯Revoke, ♯id, ♯purpose] ⋆S ⋆![♯Consent, ♯id, ♯purpose])
  | _ => ⋆⊤ₜ

def K : (Event -> TraceAssertion) := fun ns =>
  match ns with
  | [RequestDeletion, id] => ✧( 30 )⋆![♯PerformDeletion, ♯id]
  | _ => ⋆⊤ₜ
