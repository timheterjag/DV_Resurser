
module question7 where

open import ExamPrelude

module _ (_≤_ : A → A → Set) where

  data OrdListB (b : A) : Set where
    []    : OrdListB b
    consB : (x : A) → b ≤ x → OrdListB x → OrdListB b

  data OrdList : Set where
    []  : OrdList
    _∷_ : (x : A) → OrdListB x → OrdList

  infixr 5 _∷_

module _ {_≤_ : A → A → Set} where

  toListB : OrdListB _≤_ x → List A
  toListB []             = []
  toListB (consB x _ xs) = x ∷ toListB xs

  toList : OrdList _≤_ → List A
  toList []       = []
  toList (x ∷ xs) = x ∷ toListB xs

  module _ (cmp : ∀ x y → x ≤ y ∨ y ≤ x) where

    -- (a) define insertB, insert and sort (type signatures given)

    insertB : ∀ {b} (x : A) → b ≤ x → OrdListB _≤_ b → OrdListB _≤_ b
    insertB = {!!}

    insert : A → OrdList _≤_ → OrdList _≤_
    insert = {!!}

    sort : List A → OrdList _≤_
    sort = {!!}

_≤_ : Nat → Nat → Set
n ≤ m = IsTrue (n < m || n == m)

-- (b) define cmp and check that toList (sort cmp xs) does indeed sort by giving some test cases

cmp : ∀ n m → n ≤ m ∨ m ≤ n
cmp n m = {!!}

_ : toList (sort cmp (3 ∷ 2 ∷ 4 ∷ 1 ∷ [])) ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
_ = {!!} -- refl

_ : toList (sort cmp (34 ∷ 2 ∷ 41 ∷ [])) ≡ 2 ∷ 34 ∷ 41 ∷ []
_ = {!!} -- refl
