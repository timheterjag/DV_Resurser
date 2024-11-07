
module Type where

open import Prelude
open import Tactic.Deriving.Eq

infixr 8 _=>_
data Type : Set where
  nat  : Type
  _=>_ : (a b : Type) → Type

variable
  a b : Type

unquoteDecl EqType = deriveEq EqType (quote Type)
