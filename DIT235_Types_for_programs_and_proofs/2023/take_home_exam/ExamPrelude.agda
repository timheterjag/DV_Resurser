
module ExamPrelude where

open import Agda.Builtin.Equality public
open import Agda.Builtin.Nat      public
open import Agda.Builtin.Bool     public
open import Agda.Builtin.List     public
open import Agda.Builtin.Maybe    public
open import Agda.Builtin.Unit     public
open import Agda.Builtin.Sigma    public

variable
  A B C : Set
  x y : A
  xs ys : List A
  P : A → Set
  n m : Nat

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥

⊥-elim : ⊥ → A
⊥-elim ()

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : ¬ A → Dec A

infix 3 _∨_
data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

IsTrue : Bool → Set
IsTrue true  = ⊤
IsTrue false = ⊥

infixr 3 _||_
_||_ : Bool → Bool → Bool
false || x = x
true  || _ = true

infixr 4 _&&_
_&&_ : Bool → Bool → Bool
false && _ = false
true  && x = x

not : Bool → Bool
not false = true
not true  = false

-- Let's you use do-notation with Maybe
_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
nothing >>= _ = nothing
just x  >>= f = f x

_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
        (f : ∀ {x} (y : B x) → C x y) (g : ∀ x → B x) →
        ∀ x → C x (g x)
f ∘ g = λ x → f (g x)
