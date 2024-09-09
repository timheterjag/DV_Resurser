module arithexp where

-- transitive closure of a relation

data rtClos { A : Set} (R : A -> A -> Set) : A -> A -> Set where
 nil : {x : A} -> rtClos R x x
 cons : {x z : A} -> (y : A) -> R x y -> rtClos R y z -> rtClos R x z

isTransitive : {A : Set} -> (A -> A -> Set) -> Set
isTransitive {A} R = {x y z : A} -> R x y -> R y z -> R x z

rtClosTrans : {A : Set} -> (R : A -> A -> Set) -> isTransitive (rtClos R)
rtClosTrans R nil q = q
rtClosTrans R (cons y r p) q = cons y r (rtClosTrans R p q)

-- Plotkin  The Origins of Structural Operational Semantics
-- https://homepages.inf.ed.ac.uk/gdp/publications/Origins_SOS.pdf

-- one influence was the proof of confluence pages 7-9 in the paper of Martin-Löf
-- A Theory of Types 1971, that can be found online


-- typed arithmetic expression, Chapter 8 of Peirce's book

-- abstract syntax of the progrmaming language

data ArExp : Set where
 true   : ArExp
 false  : ArExp
 zero   : ArExp
 suc    : ArExp -> ArExp
 if     : ArExp -> ArExp -> ArExp -> ArExp
 prd    : ArExp -> ArExp
 isZ    : ArExp -> ArExp

-- define syntax and values v ::= vn | vb
-- vb ::= true | false
-- vn ::= zero | suc vn

data _=>_ : ArExp -> ArExp -> Set where

 =>true : {e0 e1 : ArExp} ->
   ---------------------------------------------
   if true e0 e1 => e0

 =>false : {e0 e1 : ArExp} ->
   ---------------------------------------------
   if false e0 e1 => e1

 =>if : {e e' e0 e1 : ArExp} -> e => e' ->
   ---------------------------------------------
   if e e0 e1 => if e' e0 e1


 =>suc : {e e' : ArExp} -> e => e' ->
   ---------------------------------------------
   suc e  => suc e' 


 =>isZ0 : 
   ---------------------------------------------
   isZ zero  => true

 =>isZS : {e : ArExp} ->
   ---------------------------------------------
   isZ (suc e)  => false

 =>isZ : {e e' : ArExp} ->
       e => e' ->
   ---------------------------------------------
   isZ e  => isZ e'


 =>prd0 :
            --------
     prd zero => zero

 =>prdS : {e : ArExp} -> 
            --------
     prd (suc e) => e

 =>prd : {e e' : ArExp} ->  e => e' ->
            --------
         prd e => prd e'

exp0 : ArExp
exp0 = if (isZ zero) zero (prd zero)

-- like a ProLog computation

-- test=> : if (isZ zero) zero (prd zero) => if true zero (prd zero)
-- test=> = =>if =>isZ0

_=>*_ : ArExp -> ArExp -> Set
_=>*_ = rtClos _=>_

-- like a ProLog computation

test=>* : if (isZ zero) zero (prd zero) =>* zero
test=>* = cons (if true zero (prd zero)) (=>if =>isZ0) (cons zero =>true nil)

-- test=>* : if (isZ zero) zero (prd zero) =>* zero
-- test=>* = cons (if true zero (prd zero)) (=>if =>isZ0) (cons zero =>true nil)

-- small step semantic   one step semantics

-- We define the -values- of this simple programming language

data isValnat : ArExp -> Set where
 isValnat0 : isValnat zero
 isValnatS : {e : ArExp} -> isValnat e -> isValnat (suc e)

-- v ::= bv | nv
-- bv ::= true | false
-- nv ::= zero | suc zero

data isVal : ArExp -> Set where
 Valtrue : isVal true
 Valfalse : isVal false
 Valnat : {e : ArExp} -> isValnat e -> isVal e

-- progress e is isVal e ‌∨  ∃ e' (e => e')

data progress : ArExp -> Set where
 Val : {e : ArExp} -> isVal e -> progress e
 Red : {e e' : ArExp} -> e => e' -> progress e

data ⊥ : Set where

elim-⊥ : {A : Set} -> ⊥ -> A
elim-⊥ {A} ()

¬ : Set -> Set
¬ A = A -> ⊥

isStuck : ArExp -> Set
isStuck e = ¬ (progress e)

--  some programs can be stuck...

remark : isStuck (isZ true) -- (progress (isZ true)) -> ⊥
remark (Val (Valnat ()))
remark (Red (=>isZ ()))

exSt2 : isStuck (prd true) -- (progress (isZ true)) -> ⊥
exSt2 (Val (Valnat ()))
exSt2 (Red (=>prd ()))

exP1 : progress (if (isZ zero) false false)
exP1 = Red (=>if =>isZ0)

exP2 : progress (suc zero)
exP2 = Val (Valnat (isValnatS isValnat0))

-- normal programs: a program that cannot compute
-- values, expected results of a computation
-- isZ true is -normal- but it is not a value

=>normal : ArExp -> Set
=>normal e = {e' : ArExp} -> ¬ (e => e')

lem2 : =>normal true
lem2 ()

lem0 : {e : ArExp} -> isValnat e -> =>normal e
lem0 isValnat0 ()
lem0 (isValnatS env) (=>suc h) = lem0 env h

-- a value cannot compute in one step
-- but the converse is false: there are programs that are normal but are not values

lem1 : {e : ArExp} -> isVal e -> =>normal e
lem1 Valtrue ()
lem1 Valfalse ()
lem1 (Valnat x) = lem0 x



-- big step semantics
-- direct relation between a program and the value to which this program computes to

data _⇓_ : ArExp -> ArExp -> Set where

 ⇓true : {e e0 e1 v : ArExp} -> e ⇓ true -> e0 ⇓ v ->
   ---------------------------------------------
   if e e0 e1 ⇓ v

 ⇓false : {e e0 e1 v : ArExp} -> e ⇓ false -> e1 ⇓ v ->
   ---------------------------------------------
   if e e0 e1 ⇓ v

 ⇓suc : {e v : ArExp} -> e ⇓ v ->
   ---------------------------------------------
   suc e  ⇓ suc v 

 ⇓isZ0 : {e : ArExp} -> e ⇓ zero ->
   ---------------------------------------------
   isZ e  ⇓ true

 ⇓isZS : {e v : ArExp} -> e ⇓ suc v ->
   ---------------------------------------------
   isZ e  ⇓ false

 ⇓prd0 : {e : ArExp} -> e ⇓ zero ->
            --------
     prd e ⇓ zero

 ⇓prdS : {e v : ArExp} -> e ⇓ suc v ->
            --------
     prd (suc e) ⇓ v

 v0 : zero ⇓ zero
 vtrue : true ⇓ true
 vfalse : false ⇓ false 

-- computation like ProLog

test⇓0 : if (isZ zero) zero (prd zero) ⇓ zero
test⇓0 = ⇓true (⇓isZ0 v0) v0
