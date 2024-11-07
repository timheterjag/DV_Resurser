
module TypeCheck where

open import Prelude
open import Container.Traversable
open import Term
open import Term.Show
open import Term.Parse
open import Variables

TC : Set → Set
TC A = Either String A

fail : String → TC A
fail = left

data WellTyped (Γ : Context) (e : RawTerm) : Set where
  ok : (a : Type) (t : Term Γ a) → forgetTypes t ≡ e → WellTyped Γ e

infix 2 _∷:_
pattern _∷:_ t a = ok a t refl

data InScope (Γ : Context) (x : Name) : Set where
  ok : ∀ a → (x , a) ∈ Γ → InScope Γ x

pattern dbIx_∷:_ i a = ok a i

lookupVar : ∀ Γ x → TC (InScope Γ x)
lookupVar [] x = fail $ "Not in scope: " & x
lookupVar ((y , a) ∷ Γ) x with x == y
... | yes refl = pure (ok a zero)
... | no _     = do
  dbIx i ∷: a ← lookupVar Γ x
  pure (dbIx suc i ∷: a)

_=?=_ : (a b : Type) → TC (a ≡ b)
a =?= b =
  case a == b of λ where
    (yes eq) → pure eq
    (no _)   → fail $ "Type mismatch: " & show a & " != " & show b

infer : (Γ : Context) (e : RawTerm) → TC (WellTyped Γ e)
infer Γ (var x) = do
  dbIx i ∷: a ← lookupVar Γ x
  pure (var x i ∷: a)
infer Γ (lit n) = pure (lit n ∷: nat)
infer Γ suc     = pure (suc ∷: nat => nat)
infer Γ (app e e₁) = do
  u ∷: a => b ← infer Γ e
    where u ∷: a → fail $ "Cannot apply " & show u & " of type " & show a
  v ∷: a₁ ← infer Γ e₁
  refl ← a =?= a₁
  pure (app u v ∷: b)
infer Γ (lam x a e) = do
  v ∷: b ← infer ((x , a) ∷ Γ) e
  pure (lam x v ∷: a => b)
infer Γ (natrec a) = pure (natrec ∷: _)

check : (Γ : Context) (e : RawTerm) (a : Type) → TC (Term Γ a)
check Γ e a = do
  t ∷: a₁ ← infer Γ e
  refl    ← a =?= a₁
  pure t

-- We can forget about the raw term and just keep a pair of a type
-- and a term of that type.

TypedTerm : Context → Set
TypedTerm Γ = Σ Type (Term Γ)

forgetRaw : ∀ {Γ e} → WellTyped Γ e → TypedTerm Γ
forgetRaw (t ∷: a) = a , t

-- Combining parsing and type checking
checkString : String → TC (TypedTerm [])
checkString s =
  case parseTerm s of λ where
    nothing  → fail $ "Parse error on: " & s
    (just e) → forgetRaw <$> infer [] e

-- Apply a typed term to a list of arguments. Fails if there are too many
-- arguments or their types don't match what the function expects.
applyArgs : TypedTerm Γ → List (TypedTerm Γ) → TC (TypedTerm Γ)
applyArgs t [] = pure t
applyArgs (a => b , f) ((a₁ , v) ∷ vs) = do
  refl ← a =?= a₁
  applyArgs (b , app f v) vs
applyArgs (a , v) _ = fail $ "Too many arguments to " & show v & " of type " & show a

-- We use this in the main program to combine a term from a file with arguments from
-- the command line.
checkStrings : String → List String → TC (TypedTerm [])
checkStrings f args = do
  f    ← checkString f
  args ← traverse checkString args
  applyArgs f args

-- We could go further and give some guarantee that we type check the raw term
-- returned by the parser, but since we haven't verified the parser that isn't
-- saying very much.

data WellTyped' (Γ : Context) (s : String) : Set where
  ok : ∀ (e : RawTerm) (v : WellTyped Γ e) → parseTerm s ≡ just e → WellTyped' Γ s

checkString' : (s : String) → TC (WellTyped' [] s)
checkString' s with parseTerm s in eq         -- <- the "in eq" syntax binds `eq` to a proof that parseTerm s
... | nothing = fail $ "Parse error on: " & s --    equals the patterns we match it against (`nothing` and `just e`).
... | just e  = do
  v <- infer [] e                             --    So, here we have `eq : parseTerm s ≡ just e` which is exactly
  pure (ok e v eq)                            --    what we need to provide to the `ok` constructor.
