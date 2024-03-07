
module question1 where

open import ExamPrelude

Pred : Nat → Set
Pred zero    = Bool
Pred (suc n) = Bool → Pred n

taut : (n : Nat) → Pred n → Bool
taut n p = {!!}

_ : taut 1 (λ p → p || not p) ≡ true
_ = {!!} -- refl
