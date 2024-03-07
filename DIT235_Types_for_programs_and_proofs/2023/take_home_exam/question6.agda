
module question6 where

open import ExamPrelude

data transClos (R : A → A → Set) : A → A → Set where
 []  : {x : A} → transClos R x x
 _∷_ : {x y z : A} → R x y → transClos R y z → transClos R x z

-- terms and quasi-terms

data Term : Set where
 var : Nat → Term
 lam : Term → Term
 app : Term → Term → Term
 true : Term
 false : Term

data Qterm : Set where
  clos : Term → List Qterm → Qterm
  app : Qterm → Qterm → Qterm
  true : Qterm
  false : Qterm

Env : Set
Env = List Qterm

fetch : Nat → Env → Qterm
fetch n []             = false     -- dummy value
fetch zero (v ∷ vs)    = v
fetch (suc n) (v ∷ vs) = fetch n vs

-- symbolic evaluation

eval : Term → Env → Qterm
eval (app t0 t1) vs = app (eval t0 vs) (eval t1 vs)
eval (lam t) vs = clos t vs
eval true vs = true
eval false vs = false
eval (var n) vs = fetch n vs

-- actual computation, call-by-name

infix 6 _=>_

data _=>_ : Qterm → Qterm → Set where
   Beta :    {t : Term} {vs : Env} {v : Qterm} →

             app (clos t vs) v => eval t (v ∷ vs)

   AppL :    {t t' u : Qterm}  →

             t => t' →
             ----------------------
             app t u => app t' u

_=>*_ : Qterm → Qterm → Set
e =>* e' = transClos _=>_ e e'

data Type : Set where
 bool : Type
 arrow : Type → Type → Type

-- typing relation

context : Set
context = List Type

variable
  Γ : context
  a b : Type

data Fetch : context → Nat → Type → Set where
 zero : Fetch (a ∷ Γ) zero a
 suc  : Fetch Γ n b → Fetch (a ∷ Γ) (suc n) b

data hasType : context → Term → Type → Set where
 true  : hasType Γ true bool
 false : hasType Γ false bool
 var   : Fetch Γ n a → hasType Γ (var n) a
 app   : ∀ {t u} → hasType Γ t (arrow a b) → hasType Γ u a → hasType Γ (app t u) b
 lam   : ∀ {u} → hasType (a ∷ Γ) u b → hasType Γ (lam u) (arrow a b)

-- reducibility predicate

data redbool : Qterm → Set where
 true  : {t : Qterm} → t =>* true  → redbool t
 false : {t : Qterm} → t =>* false → redbool t

red : Type → Qterm → Set
red bool t = redbool t
red (arrow a b) t = (u : Qterm) → red a u → red b (app t u)

redC : context → Env → Set
redC [] [] = ⊤
redC (a ∷ Γ) (u ∷ us) = red a u ∧ redC Γ us
redC _ _ = ⊥

redT : red bool true
redT = {!!}

redF : red bool false
redF = {!!}

upRed : (a : Type) {t u : Qterm} → t => u → red a u → red a t
upRed = {!!}

lemFetch : (Γ : context) (rho : Env) → redC Γ rho
         → (n : Nat) {a : Type} → Fetch Γ n a → red a (fetch n rho)
lemFetch = {!!}

lemEval : (Γ : context) (rho : Env) → redC Γ rho
        → (t : Term) {a : Type} → hasType Γ t a → red a (eval t rho)
lemEval = {!!}

theorem1 : {t : Term} → hasType [] t bool → redbool (eval t [])
theorem1 {t} = {!!}

id : Term
id = lam (var zero)

ext1 : Term
ext1 = app id true

dext1 : hasType [] ext1 bool
dext1 = {!!}

test1 : redbool (eval ext1 [])
test1 = {!!}

prime : Type → Type
prime a = arrow a a

twice : Term
twice = lam (lam (app (var 1) (app (var 1) (var 0))))

twices : Nat → Term
twices zero = twice
twices (suc n) = app (twices n) twice

lemtwice : (a : Type) → hasType [] twice (prime (prime a))
lemtwice = {!!}

lemtwices : (n : Nat) (a : Type) → hasType [] (twices n) (prime (prime a))
lemtwices = {!!}

ex2 : Nat → Term
ex2 n = app (app (twices n) id) true

dext2 : (n : Nat) → hasType [] (ex2 n) bool
dext2 n = {!!}

test2 : (n : Nat) → red bool (eval (ex2 n) [])
test2 n = {!!}
