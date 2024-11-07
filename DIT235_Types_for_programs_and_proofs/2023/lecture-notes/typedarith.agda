module typedarith where

open import arithexp

-- Types appeared first in -logic- in order to prevent paradoxes
-- Bertrand Russell  1901 ---> 1908
-- 1908 Types versus Sets
-- set theory is an axiomatic system

-- The theory of Russell was simplified by Alonzo Church 1940
-- The systems HOL and Isabelle-HOL are using Church's system of simply typed lambda-calculus

-- In this file, we only have two types Natural numbers and Boolean

data Type : Set where
 NN : Type
 BB : Type

-- not to be confused with the data types Nat and Bool!

-- we also represent the typing relation as an inductively defined relation, using propositions as Types/Sets

data _ofType_ : ArExp -> Type -> Set where

 typet : true ofType BB
 
 typef : false ofType BB
 
 typeif : {T : Type} -> {e e0 e1 : ArExp} ->
      e ofType BB -> e0 ofType T -> e1 ofType T ->
       ---------------------------------------
              if e e0 e1 ofType T

 type0 : zero ofType NN

 typeS : {e : ArExp} -> e ofType NN -> 
         --------------------------
               suc e ofType NN
               

 typep : {e : ArExp} -> e ofType NN ->
         --------------------------
               prd e ofType NN
               
 typeZ : {e : ArExp} -> e ofType NN ->
         --------------------------
               isZ e ofType BB

exp0N : (if (isZ zero) zero (prd zero)) ofType NN
exp0N = typeif (typeZ type0) type0 (typep type0)

-- a derivation tree of a typing judgement e ofType T
-- is a term of this type written only with constructors!

-- uniqueness of typing 8.4.2


data _≡_ {A : Set} (a : A) : A -> Set where
 refl : a ≡ a

infix 4 _≡_


uniqueness : (e : ArExp) -> {T T' : Type} -> e ofType T -> e ofType T' -> T ≡ T'
uniqueness true {.BB} {.BB} typet typet = refl
uniqueness false {.BB} {.BB} typef typef = refl
uniqueness zero {.NN} {.NN} type0 type0 = refl
uniqueness (suc e) {.NN} {.NN} (typeS x) (typeS x₁) = refl
uniqueness (if e e₁ e₂) {T} {T'} (typeif x x₂ x₃) (typeif x₁ x₄ x₅) = uniqueness e₁ x₂ x₄
uniqueness (prd e) {.NN} {.NN} (typep x) (typep x₁) = refl
uniqueness (isZ e) {.BB} {.BB} (typeZ x) (typeZ x₁) = refl

-- exercise 8.3.6   subject expansion

exp1 : ArExp
exp1 = if true zero false

remark7 : exp1 => zero
remark7 = =>true

remark8 : ¬ (exp1 ofType NN)
remark8 (typeif typet type0 ())

-- subject reduction/preservation   8.3.3

preservation : {e e' : ArExp} -> {T : Type} ->
    e ofType T ->
    e => e' ->
    --------------------
    e' ofType T

preservation (typeif typet eT0 eT1) =>true = eT0
preservation (typeif typef eT0 eT1) =>false = eT1
preservation (typeif eT eT0 eT1) (=>if ee') =        --  if e e0 e1 => if e' e0 e1  because e => e'   eT0   e0 ofType T
  typeif (preservation eT ee') eT0 eT1               --  e ofType Bool
preservation (typeS eT) (=>suc ee') = typeS (preservation eT ee')
preservation (typeZ type0) =>isZ0 = typet
preservation (typeZ (typeS eT)) =>isZS = typef
preservation (typeZ eT) (=>isZ ee') = typeZ (preservation eT ee')
preservation (typep type0) =>prd0 = type0
preservation (typep (typeS eT)) =>prdS = eT
preservation (typep eT) (=>prd ee') = typep (preservation eT ee')    

-- progress 8.3.2

typeprog : {e : ArExp} -> {T : Type} -> e ofType T -> progress e

typeprog typet = Val Valtrue
typeprog typef = Val Valfalse
typeprog (typeif {T} {e} {e0} {e1} eT eT0 eT1) = rem1 rem eT
 where rem : progress e
       rem = typeprog eT
       rem1 : {u : ArExp} -> progress u -> u ofType BB -> progress (if u e0 e1)
       rem1 (Val Valtrue) typet = Red =>true
       rem1 (Val (Valnat ())) typet
       rem1 (Val Valfalse) typef = Red =>false
       rem1 (Val (Valnat ())) typef
       rem1 (Val (Valnat ())) (typeif uBB uBB₁ uBB₂)
       rem1 (Val (Valnat ())) (typeZ uBB)
       rem1 (Red x) uBB = Red (=>if x)
typeprog type0 = Val (Valnat isValnat0)
typeprog (typeS {e} eT) = rem1 rem eT where
  rem : progress e
  rem = typeprog eT
  rem1 : {u : ArExp} -> progress u -> u ofType NN -> progress (suc u)
  rem1 (Val (Valnat ())) (typeif uNN uNN₁ uNN₂)
  rem1 (Val (Valnat isValnat0)) type0 = Val (Valnat (isValnatS isValnat0))
  rem1 (Val (Valnat x)) (typeS uNN) = Val (Valnat (isValnatS x))
  rem1 (Val (Valnat x)) (typep uNN) = Val (Valnat (isValnatS x))
  rem1 (Red x) uNN = Red (=>suc x)
typeprog (typep {e} eT) = rem1 rem eT where
  rem : progress e
  rem = typeprog eT
  rem1 : {u : ArExp} -> progress u -> u ofType NN -> progress (prd u)
  rem1 (Val (Valnat ())) (typeif uNN uNN₁ uNN₂)
  rem1 (Val (Valnat isValnat0)) type0 =  Red =>prd0
  rem1 (Val (Valnat x)) (typeS uNN) = Red =>prdS
  rem1 (Val (Valnat ())) (typep uNN)
  rem1 (Red x) uNN = Red (=>prd x)
typeprog (typeZ {e} eT) = rem1 rem eT where
  rem : progress e
  rem = typeprog eT
  rem1 : {u : ArExp} -> progress u -> u ofType NN -> progress (isZ u)
  rem1 (Val (Valnat ())) (typeif uNN uNN₁ uNN₂)
  rem1 (Val (Valnat x)) type0 = Red =>isZ0
  rem1 (Val (Valnat x)) (typeS uNN) = Red =>isZS
  rem1 (Val (Valnat ())) (typep uNN)
  rem1 (Red x) uNN = Red (=>isZ x)

-- safety = progress + preservation tell us that a well-typed term can never reach
-- a stuck state during evaluation

-- the next proof is by induction on =>*
-- also known as computational induction

-- this is a powerful method which works even if we have programs that may loop

-- http://www.cs.tau.ac.il/~nachumd/term/MNV.pdf
-- Z. Manna 1973 inductive methods for proving properties of programs

-- Milner's slogan   "well-typed programs can't go wrong"
-- safety = progress + preservation

-- Interesting that "safety" was also the reason why Russell introduced the notion of types in the first place


-- This was proven using operational semantics in the paper of Wright and Felleisein
-- A Syntactic Approach to Type Soundness


theorem : {e e' : ArExp} -> {T : Type} -> e ofType T -> e =>* e' -> progress e'
theorem eT nil = typeprog eT
theorem {T = T} eT (cons {e} {e'} e1 r e1e') = theorem rem1 e1e'    where
  rem1 : e1 ofType T
  rem1 = preservation eT r

-- if a program is well-typed and it terminates, then it terminates on a value
-- follows from the theorem

result : {e : ArExp} -> {T : Type} -> e ofType T -> =>normal e -> isVal e
result {e} eT = rem1 rem
 where
   rem : progress e
   rem = typeprog eT
   rem1 : {x : ArExp} -> progress x -> =>normal x -> isVal x
   rem1 (Val y) xn = y
   rem1 (Red y) xn = elim-⊥ (xn y)

{-
testZ : Nat -> Bool
testZ zero = true
testZ (suc n) = false

mutual 
 valB : (e : ArExp) -> e ofType BB -> Bool
 valN : (e : ArExp) -> e ofType NN -> Nat
 
 valB true eB = true
 valB false eB = false
 valB zero ()
 valB (suc e) ()
 valB (if e e0 e1) (typeif eB eB0 eB1) = if (valB e eB) then (valB e0 eB0) else ((valB e1 eB1)) 
 valB (prd e) ()
 valB (isZ e) (typeZ eN) = testZ (valN e eN)

 valN true ()
 valN false ()
 valN zero eN = zero
 valN (suc e) (typeS eN) = suc (valN e eN)
 valN (if e e0 e1) (typeif eB eN0 eN1) = if (valB e eB) then (valN e0 eN0) else (valN e1 eN1) 
 valN (prd e) (typep eN) = pred (valN e eN)
 valN (isZ e) ()

valT : Type -> Set
valT BB = Bool
valT NN = Nat

val : (e : ArExp) (T : Type) -> e ofType T -> valT T
val e NN eT = valN e eT
val e BB eT = valB e eT

-}
