{-

  Lecture 11: A case study in dependently typed programming
                Type checking the simply typed λ-calculus

-}

module Term where

open import Prelude
open import Type public
open import Variables

Name = String

-- λ-terms with natural numbers
data RawTerm : Set where
  var : (x : Name) → RawTerm
  lit : (n : Nat) → RawTerm
  suc : RawTerm
  app : (e e₁ : RawTerm) → RawTerm
  lam : (x : Name) (a : Type) (e : RawTerm) → RawTerm
  natrec : (a : Type) → RawTerm

private
  -- λ (x : nat) . suc x
  ex₁ : RawTerm
  ex₁ = lam "x" nat (app suc (var "x"))

Context : Set
Context = List (Name × Type)

variable
  Γ : Context

infix 1 _∈_
data _∈_ (x : A) : List A → Set where
  zero : x ∈ x ∷ xs
  suc  : x ∈ xs → x ∈ y ∷ xs

private
  2∈0123 : (2 ofType Nat) ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
  2∈0123 = suc (suc zero)

data Term (Γ : Context) : Type → Set where
  lit : (n : Nat) → Term Γ nat
  suc : Term Γ (nat => nat)
  app : (s : Term Γ (a => b)) (t : Term Γ a) → Term Γ b
  lam : (x : Name) (t : Term ((x , a) ∷ Γ) b) → Term Γ (a => b)
  var : (x : Name) → (x , a) ∈ Γ → Term Γ a
  natrec : Term Γ (a => (nat => a => a) => nat => a)

infixl 9 _∙_
pattern _∙_ x y = app x y

forgetTypes : Term Γ a → RawTerm
forgetTypes (lit n)           = lit n
forgetTypes suc               = suc
forgetTypes (app s t)         = app (forgetTypes s) (forgetTypes t)
forgetTypes (lam {a = a} x t) = lam x a (forgetTypes t)
forgetTypes (var x i)         = var x
forgetTypes (natrec {a = a})  = natrec a
