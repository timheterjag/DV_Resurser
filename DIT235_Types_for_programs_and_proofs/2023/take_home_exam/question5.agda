
module question5 where

open import ExamPrelude

{-# TERMINATING #-}  -- Turning off the termination checker
modSuc' : Nat → Nat → Nat
modSuc' n m with n < suc m
... | true  = n
... | false = modSuc' (n - suc m) m

mod' : Nat → Nat → Nat
mod' n zero    = zero
mod' n (suc m) = modSuc' n m

data Terminating (R : A → A → Set) (a : A) : Set where
  node : (∀ {b} → R a b → Terminating R b) → Terminating R a

data Down : Nat → Nat → Set where
  suc-zero : Down (suc n) zero
  suc-suc  : Down n m → Down (suc n) (suc m)

-- (a) Prove that Down is a terminating relation.

-- Optional lemma
term-suc : ∀ {n} → Terminating Down n → Terminating Down (suc n)
term-suc t = {!!}

termination : ∀ n → Terminating Down n
termination n = {!!}

-- (b) Prove Down (suc n) (suc n - suc m)

-- Optional lemma
down-suc : Down n m → Down (suc n) m
down-suc d = {!!}

down-minus : ∀ n m → Down (suc n) (suc n - suc m)
down-minus n m = {!!}

-- (c) Define a terminating modSuc

modSuc : (n m : Nat) → Terminating Down n → Nat
modSuc n m t = {!!}

mod : Nat → Nat → Nat
mod n m = {!!}

_ : mod 17 5 ≡ 2
_ = {!!} -- refl
