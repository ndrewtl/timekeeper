namespace Timekeeper.Notation

class Negation (α : Type) where
  not : α -> α

class Disjunction (α : Type) where
  or : α -> α -> α

class Conjunction (α : Type) where
  and : α -> α -> α

class Implication (α : Type) where
  implies : α -> α -> α

prefix:max "⋆¬"   => Negation.not
-- star-impl
infixl:272 " ⋆∧ " => Conjunction.and
infixl:271 " ⋆∨ " => Disjunction.or
infixr:270 " ⋆→ " => Implication.implies
