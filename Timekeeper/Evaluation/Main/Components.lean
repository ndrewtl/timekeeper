import Timekeeper.Language.Command
import Timekeeper.Lemma.Soundness.Future
import Timekeeper.Lemma.GeneralAssertion
import Timekeeper.Lemma.Soundness.Future
import Timekeeper.Evaluation.Main.Constants
import Timekeeper.Evaluation.Main.Specification
import Timekeeper.Evaluation.Main.Invariants

namespace Timekeeper.Evaluation.Main
open Command
open GeneralAssertion
open GeneralAssertion.Models
open Soundness.Future

def block₁ : Command :=
  set ⋆$"i" ⋆:= ♯0 ⋆;
  set ⋆$"consent_db" ⋆:= ⋆{}

def block₂ : Command :=
  set ⋆$"k" ⋆:= ♯0 ⋆;
  set ⋆$"deletion_requests" ⋆:= ⋆{}

def block₃ : Command :=
  -- Increment both idx and k
  set ⋆$"i" ⋆:= ⋆$"i" ⋆+ ♯1 ⋆;
  set ⋆$"k" ⋆:= ⋆$"k" ⋆+ ♯1

def consent_branch : Command :=
  set ⋆$"user_id" ⋆:= (⋆$"action")[♯1]ₑ ⋆;
  set ⋆$"purpose" ⋆:= (⋆$"action")[♯2]ₑ ⋆;
  -- consent_db[user_id][purpose] := 1
  set ⋆$"consent_db" ⋆:= (⋆$"consent_db")[⋆$"user_id" := (⋆$"consent_db")[⋆$"user_id"]ₑ[⋆$"purpose" := ♯1]ₑ]ₑ ⋆;
  emit [♯Consent, ⋆$"user_id", ⋆$"purpose"]

def revoke_branch : Command :=
  set ⋆$"user_id" ⋆:= (⋆$"action")[♯1]ₑ ⋆;
  set ⋆$"purpose" ⋆:= (⋆$"action")[♯2]ₑ ⋆;
  set ⋆$"consent_db" ⋆:= (⋆$"consent_db")[⋆$"user_id" := (⋆$"consent_db")[⋆$"user_id"]ₑ[⋆$"purpose" := ♯0]ₑ]ₑ ⋆;
  emit [♯Revoke, ⋆$"user_id", ⋆$"purpose"]

def use_branch : Command :=
  set ⋆$"user_id" ⋆:= (⋆$"action")[♯1]ₑ ⋆;
  set ⋆$"purpose" ⋆:= (⋆$"action")[♯2]ₑ ⋆;
  if: (⋆$"consent_db")[⋆$"user_id"]ₑ[⋆$"purpose"]ₑ ⋆= ♯TrueVal then:
    set ⋆$"output" ⋆:= (⋆$"data_store")[⋆$"user_id"]ₑ ⋆;
    emit [♯Use, ⋆$"user_id", ⋆$"purpose"]
  else:
    -- Use disallowed
    skip
  end

def request_deletion_branch : Command :=
  set ⋆$"user_id" ⋆:= (⋆$"action")[♯1]ₑ ⋆;
  -- the creation time is the same as the index of the RequestDeletion event
  set ⋆$"request" ⋆:= ⋆{}[♯0 := ♯RequestDeletion]ₑ[♯1 := ⋆$"user_id"]ₑ[♯2 := ℓ]ₑ ⋆;
  set ⋆$"deletion_requests" ⋆:= (⋆$"deletion_requests")[⋆$"k" := ⋆$"request"]ₑ ⋆;
  emit [♯RequestDeletion, ⋆$"user_id"]

def resolve_block : Command :=
  set ⋆$"request" ⋆:= (⋆$"deletion_requests")[⋆$"k'"]ₑ ⋆;
  if: (⋆$"request")[ ♯0 ]ₑ ⋆= ♯RequestDeletion
    then:
      set ⋆$"user_id" ⋆:= (⋆$"request")[♯1]ₑ ⋆;
      set ⋆$"request_time" ⋆:= (⋆$"request")[♯2]ₑ ⋆;
      set ⋆$"data_store" ⋆:= (⋆$"data_store")[⋆$"user_id" := ♯0]ₑ ⋆;
      emit [♯PerformDeletion, ⋆$"user_id"] ⋆;
      resolve ( ✧( 30 ) ⋆!([♯PerformDeletion, ⋆$"user_id"]) ⋆@ ⋆$"request_time")
    else:
      -- No deletion was requested, so none must be performed
      skip
  end ⋆;
  set ⋆$"k'" ⋆:= ⋆$"k'" ⋆+ ♯1
