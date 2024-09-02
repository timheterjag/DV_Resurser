
module question4 where

open import ExamPrelude

data Any (P : A → Set) : List A → Set where
  zero : P x → Any P (x ∷ xs)
  suc  : Any P xs → Any P (x ∷ xs)

data All (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : P x → All P xs → All P (x ∷ xs)

-- (a)

q4a : ∀ xs → ¬ (Any P xs) → All (¬ ∘ P) xs
q4a = {!!}

-- (b)

q4b : (∀ x → Dec (P x)) → (xs : List A) → ¬ (Any (¬ ∘ P) xs) → All P xs
q4b = {!!}
