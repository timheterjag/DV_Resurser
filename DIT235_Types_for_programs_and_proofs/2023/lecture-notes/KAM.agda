module KAM where

-- the paper of Landin   A mechanical evaluation of expressions 1964
-- describes a call-by-value version of the evaluation presented in this file

-- This is the KAM   Krivine Abstract Machine which presents a call-by-name version of Landin's paper


data Nat : Set where
 zero : Nat
 suc  : Nat -> Nat

one : Nat
one = suc zero

data list (A : Set) : Set where
 nil  : list A
 cons : A -> list A -> list A

-- we can think of a list as a stack

_·_ : {A : Set} -> A -> list A -> list A
x · xs = cons x xs

-- or as an environment 

update : {A : Set} -> list A -> A -> list A
update xs x = cons x xs

-- lambda terms with de Bruijn notation

data Term : Set where
 var : Nat -> Term
 lam : Term -> Term
 app : Term -> Term -> Term

-- terms representing computations where we stop substitution at lambda abstractions

data Qterm : Set where
  clos : Term -> list Qterm -> Qterm
  app : Qterm -> Qterm -> Qterm


Env : Set
Env = list Qterm

fetch : Nat -> Env -> Qterm
fetch n nil               = clos (var zero) nil     -- dummy value
fetch zero (cons v ρ)     = v
fetch (suc n) (cons v ρ)  = fetch n ρ


-- we stop substitution at lambda abstractions

substV : Term -> Env -> Qterm

substV (app t0 t1) ρ = app (substV t0 ρ) (substV t1 ρ)
substV (lam t) ρ     = clos t ρ
substV (var n) ρ     = fetch n ρ

infix 6 _=>_

data _=>_ : Qterm -> Qterm -> Set where

   Beta :    {t : Term} {ρ : Env} {v : Qterm} ->
   
             app (clos t ρ) v  => substV t (update ρ v) 


   AppL :    {t t' u : Qterm}  -> 
   
                   t => t'     ->
             ----------------------
             app t u => app t' u

-- the evaluation is much simpler formally
-- than doing substitution under abstraction

data rtClos {A : Set} (R : A -> A -> Set) : A -> A -> Set where
 nil  : {x : A} -> rtClos R x x
 cons : {x y z : A} -> R x y -> rtClos R y z -> rtClos R x z

rtClosTrans : {A : Set} -> (R : A -> A -> Set) -> {x y z : A} ->
    rtClos R x y -> rtClos R y z -> rtClos R x z

rtClosTrans R nil q = q
rtClosTrans R (cons r p) q = cons r (rtClosTrans R p q)

_=>*_ : Qterm -> Qterm -> Set
e =>* e' = rtClos _=>_ e e'

-- test on evaluating id id   =   (λx x) (λx x)
-- in Agda id id is represented by the Term

-- t   =   App (Lam (Ind zero)) (Lam (Ind zero)

-- Qterm t  Nil Nil -> ... -> ...

i0 : Term
i0 = var zero

i1 : Term
i1 = var one

idT : Term
idT = lam i0

deltaT : Term
deltaT = lam (app i0 i0)

idV : Qterm
idV = substV idT nil

deltaV : Qterm
deltaV = substV deltaT nil

omegaV : Qterm 
omegaV = app deltaV deltaV

test : app idV idV => clos (var zero) nil
test = Beta
     
test1 : omegaV => omegaV
test1 = Beta
     
--  State t Nil Nil   -> ... ->   State (λ 0) Nil Nil
--  where t  was  App (λ 0) (λ 0)

-- reformulation as a machine which takes as a state a Qterm and a stack of Qterm

data State : Set where 
 state : Qterm -> list Qterm -> State

infix 6 _↦_


data _↦_ : State -> State -> Set where

 push : {v0 v1 : Qterm} -> {vs : list Qterm} -> state (app v0 v1) vs ↦ state v0 (v1 · vs)

 pop  : {t : Term} -> {ρ : Env} -> {v : Qterm} -> {vs : list Qterm} ->
        state (clos t ρ) (cons v vs) ↦ state (substV t (update ρ v)) vs


infix 6 _↦*_

_↦*_ : State -> State -> Set
e ↦* e' = rtClos _↦_ e e'

infixr 4 _↦<_>_

_↦<_>_ : ∀ (x : State) {y z : State }
    → x  ↦  y
    → y  ↦* z
      -----
    → x  ↦* z
x ↦< p > q  =  cons p q

_end : (x : State ) → x  ↦* x
x end = nil

oneStep : {x y : State} -> x ↦ y -> x ↦* y
oneStep p = cons p nil

-- example of an evaluation

q0 : Qterm
q0 = substV (app deltaT idT) nil

exq0 :   state q0 nil ↦* state idV nil
exq0 =
 state (app (clos (app i0 i0) nil) idV) nil      ↦< push >
 state (clos (app i0 i0) nil) (idV · nil)        ↦< pop  >
 state (app idV idV) nil                         ↦< push >
 state idV (idV · nil)                           ↦< pop  >
 state idV nil                                   end

exq01 :   state q0 nil ↦* state idV nil
exq01 = cons push (cons pop (cons push (cons pop nil)))

q1 : Qterm
q1 = substV deltaT nil

q2 : Qterm
q2 = app q1 q1

exq1 : state q2 nil ↦* state q2 nil
exq1 =
 state q2 nil              ↦< push >
 state q1 (q1 · nil)       ↦< pop >
 state q2 nil              end
