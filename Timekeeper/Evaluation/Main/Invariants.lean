import Timekeeper.Logic.Assertion.GeneralAssertion
import Timekeeper.Evaluation.Main.Constants

namespace Timekeeper.Evaluation.Main

-- Whenever consent_db[id][purpose] is set, then consent must be held
def consent_invariant : GeneralAssertion :=
  ⋆∀ "id": ⋆∀ "purpose":
    (⋆$"consent_db")[⋆^"id"]ₑ[⋆^"purpose"]ₑ ⋆= ♯TrueVal ⋆→
    ⋆¬⋆![♯Revoke, ⋆^"id", ⋆^"purpose"] ⋆S ⋆![♯Consent, ⋆^"id", ⋆^"purpose"] ⋆@ ℓ ⋆- ♯1

-- This is consent_invariant, excluding user_id and purpose
def consent_invariant' : GeneralAssertion :=
  ⋆∀ "id": ⋆∀ "purpose":
    ⋆¬(⋆^"id" ⋆= ⋆$"user_id" ⋆∧ ⋆^"purpose" ⋆= ⋆$"purpose") ⋆→
    (⋆$"consent_db")[⋆^"id"]ₑ[⋆^"purpose"]ₑ ⋆= ♯TrueVal ⋆→
    ⋆¬⋆![♯Revoke, ⋆^"id", ⋆^"purpose"] ⋆S ⋆![♯Consent, ⋆^"id", ⋆^"purpose"] ⋆@ ℓ ⋆- ♯1

-- Whenever deletion_requests[idx][0] is RequestDeletion, then
-- the corresponding id must be deleted 30 from the given time
def deletion_invariant₁ : GeneralAssertion :=
  ⋆∀ "idx":
    ⋆^"idx" ⋆< ⋆$"k" ⋆→
    (⋆$"deletion_requests")[⋆^"idx"]ₑ[ ♯0 ]ₑ ⋆= ♯RequestDeletion ⋆→
    ✧( 30 ) ⋆![♯PerformDeletion, (⋆$"deletion_requests")[ ⋆^"idx" ]ₑ[ ♯1 ]ₑ] ⋆@
    (⋆$"deletion_requests")[⋆^"idx"]ₑ[ ♯2 ]ₑ

def deletion_invariant₂ : GeneralAssertion :=
  ⋆∀ "idx":
    ⋆$"k'" ⋆≤ ⋆^"idx" ⋆∧ ⋆^"idx" ⋆< ⋆$"k" ⋆→
    (⋆$"deletion_requests")[⋆^"idx"]ₑ[ ♯0 ]ₑ ⋆= ♯RequestDeletion ⋆→
    ✧( 30 ) ⋆![♯PerformDeletion, (⋆$"deletion_requests")[ ⋆^"idx" ]ₑ[ ♯1 ]ₑ] ⋆@
    (⋆$"deletion_requests")[⋆^"idx"]ₑ[ ♯2 ]ₑ

def request_deletion_invariant₁ : GeneralAssertion :=
  ⋆∀ "idx":
    (⋆^"idx" ⋆< ⋆$"k" ⋆→
    (⋆$"deletion_requests")[⋆^"idx"]ₑ[ ♯0 ]ₑ ⋆= ♯RequestDeletion ⋆→
    ℓ ⋆- (⋆$"k" ⋆- ⋆^"idx") ⋆≤ (⋆$"deletion_requests")[⋆^"idx"]ₑ[ ♯2 ]ₑ ⋆∧
    (⋆$"deletion_requests")[⋆^"idx"]ₑ[ ♯2 ]ₑ ⋆< ℓ)
    ⋆∧ ( ⋆$"k" ⋆≤ ⋆^"idx" ⋆→
    (⋆$"deletion_requests")[⋆^"idx"]ₑ ⋆= ⋆{})

def request_deletion_invariant₁' : GeneralAssertion :=
  ⋆∀ "idx":
    (⋆^"idx" ⋆< ⋆$"k" ⋆→
    (⋆$"deletion_requests")[⋆^"idx"]ₑ[ ♯0 ]ₑ ⋆= ♯RequestDeletion ⋆→
    ℓ ⋆- (⋆$"k" ⋆- ⋆^"idx") ⋆≤ (⋆$"deletion_requests")[⋆^"idx"]ₑ[ ♯2 ]ₑ ⋆∧
    (⋆$"deletion_requests")[⋆^"idx"]ₑ[ ♯2 ]ₑ ⋆< ℓ)
    ⋆∧ ( ⋆$"k" ⋆+ ♯1 ⋆≤ ⋆^"idx" ⋆→
    (⋆$"deletion_requests")[⋆^"idx"]ₑ ⋆= ⋆{})

def request_deletion_invariant₂ : GeneralAssertion :=
  ⋆∀ "idx":
    ⋆$"k'" ⋆≤ ⋆^"idx" ⋆∧ ⋆^"idx" ⋆< ♯30 ⋆→
    (⋆$"deletion_requests")[⋆^"idx"]ₑ[♯0]ₑ ⋆= ♯RequestDeletion ⋆→
    ℓ ⋆≤ (⋆$"deletion_requests")[⋆^"idx"]ₑ[ ♯2 ]ₑ ⋆+ ♯30 ⋆- ⋆^"idx" ⋆+ ⋆$"k'" ⋆∧
    (⋆$"deletion_requests")[⋆^"idx"]ₑ[ ♯2 ]ₑ ⋆< ℓ

def counter_invariant₁ : GeneralAssertion :=
  ⋆$"k" ⋆< ♯30

def counter_invariant₁' : GeneralAssertion :=
  ⋆$"k" ⋆≤ ♯30

def counter_invariant₂ : GeneralAssertion :=
  ⋆$"k" ⋆= ♯30 ⋆∧ ⋆$"k'" ⋆< ♯30

-- Same as the above, but with ≤ substituted for <
def counter_invariant₂' : GeneralAssertion :=
  ⋆$"k" ⋆= ♯30 ⋆∧ ⋆$"k'" ⋆≤ ♯30
