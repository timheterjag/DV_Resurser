
module Examples where

open import Prelude

open import Type
open import TypeCheck
open import Term
open import Term.Show
open import Term.Eval
open import Term.Parse

plus : RawTerm
plus = lam "n" nat (natrec nat ∙ var "n" ∙ lam "_" nat suc)

times : RawTerm
times = lam "n" nat (natrec nat ∙ lit 0 ∙ lam "_" nat (plus ∙ var "n"))

fac : RawTerm
fac = natrec nat ∙ lit 1 ∙ lam "n" nat (times ∙ (suc ∙ var "n"))

checkFac : ∀ Γ → TC (Term Γ (nat => nat))
checkFac Γ = check Γ fac (nat => nat)

evalRaw : ∀ a → RawTerm → Either String (Value a)
evalRaw a e =
  case check [] e a of λ where
    (left err) → left err
    (right t)  → right (eval t [])
