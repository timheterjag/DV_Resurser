module Lecture3 where

open import Lecture2
open import Agda.Builtin.List

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

data _∧_ (A B : Set) : Set where
  pair : A → B → A ∧ B

remark1 : {A : Set} → A → ⊤
remark1 = λ _ → tt

test0 : Nat → Bool
test0 zero = true
test0 (suc x) = false

exFalso : {A : Set} → ⊥ → A 
exFalso {A} x = {!!}

¬ : Set → Set
¬ A = A → ⊥

exOr : {A B C D : Set} → (A → C) → (B → C) → A ∨ B → C ∨ D
exOr f g (inl x) = inl (f x)
exOr f g (inr x) = inl (g x)

∨ᵢ₁ : {A B : Set} → A → A ∨ B
∨ᵢ₁ = inl

∨ᵢ₂ : {A B : Set} → B → A ∨ B
∨ᵢ₂ = inr

∨ₑ : { A B C : Set} → (A → C) → (B → C) → A ∨ B → C
∨ₑ f g (inl x) = f x
∨ₑ f g (inr x) = g x

∨-commutative : {A B : Set} → A ∨ B → B ∨ A
∨-commutative (inl x) = inr x
∨-commutative (inr x) = inl x

∧-commutative : {A B : Set} → A ∧ B → B ∧ A
∧-commutative (pair x x₁) = pair x₁ x

∧ᵢ : {A B : Set} → A → B → A ∧ B
∧ᵢ = pair

excluded-middle : {A B : Set} → A ∨ ¬ A
excluded-middle = {!!}

Forall : {A : Set} → (A → Set) → Set
Forall {A} P = (x : A) → P x

induction : (P : Nat → Set) → P zero → ((n : Nat) → P n → P (suc n)) → (n : Nat) → P n
induction P base ih zero = base
induction P base ih (suc n) = induction (λ z → P (suc z)) (ih zero base) (λ n → ih (suc n)) n

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → (b : B a) → Σ A B


-- Sigma elimination
Σₑ : {A : Set} {B : A → Set} {C : Set} → ((x : A) → B x → C) → Σ A B → C
Σₑ f (a , b) = f a b

∃ : {A : Set} → (A → Set) → Set
∃ {A} = Σ A

isTrue : Bool → Set
isTrue false = ⊥
isTrue true = ⊤

-- {x : A | B x} == Σ x:A B x == ∃ x:A B x

isEven : Nat → Bool
isEven zero = true
isEven (suc n) = not (isEven n)

Even : Set
Even = Σ Nat (λ n → isTrue (isEven n))

{-

-- Exercise --
Prove: ¬ ¬ (A ∨ ¬ A)
-}

negnegLem : {A : Set} → ¬ (¬ (A ∨ ¬ A))
negnegLem {A} = λ z → z (inr λ y → z (inl y))
