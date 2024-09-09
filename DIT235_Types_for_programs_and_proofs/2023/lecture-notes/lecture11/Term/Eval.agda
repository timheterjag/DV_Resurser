
module Term.Eval where

open import Prelude
open import Term
open import Variables

Value : Type → Set
Value nat      = Nat
Value (a => b) = Value a → Value b

data Env : Context → Set where
  []  : Env []
  _∷_ : Value a → Env Γ → Env ((x , a) ∷ Γ)

lookupVar : (x , a) ∈ Γ → Env Γ → Value a
lookupVar zero    (v ∷ ρ) = v
lookupVar (suc i) (v ∷ ρ) = lookupVar i ρ

natrecE : A → (Nat → A → A) → Nat → A
natrecE z s  zero   = z
natrecE z s (suc n) = s n (natrecE z s n)

eval : Term Γ a → Env Γ → Value a
eval (lit n)   ρ = n
eval suc       ρ = suc
eval (app s t) ρ = eval s ρ (eval t ρ)
eval (lam x t) ρ = λ v → eval t (v ∷ ρ)
eval (var x i) ρ = lookupVar i ρ
eval natrec    ρ = natrecE

-- λ x . suc (suc x)
tm₁ : Term [] (nat => nat)
tm₁ = lam "x" (suc ∙ (suc ∙ var "x" zero))

tm₂ : Term [] nat
tm₂ = tm₁ ∙ lit 5
