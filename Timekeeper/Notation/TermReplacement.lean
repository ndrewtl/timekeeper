namespace Timekeeper.Notation

-- Here, α represents term within which something is replaced, β the replacee,
-- and γ the replacer
class TermReplacement (α β : Type) where
  γ : Type
  replace : α -> β -> γ -> α

notation:370 σ "[" x " ↦ " n "]" => TermReplacement.replace σ x n
