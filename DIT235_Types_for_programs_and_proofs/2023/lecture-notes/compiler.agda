module compiler where


-- open import progress

-- transitive closure of a relation

data rtClos { A : Set} (R : A -> A -> Set) : A -> A -> Set where
 nil : {x : A} -> rtClos R x x
 cons : {x z : A} -> (y : A) -> R x y -> rtClos R y z -> rtClos R x z

-- compare with definition of concatenation of lists or
-- of addition

isTransitive : {A : Set} -> (A -> A -> Set) -> Set
isTransitive {A} R = {x y z : A} -> R x y -> R y z -> R x z

rtClosTrans : {A : Set} -> (R : A -> A -> Set) -> isTransitive (rtClos R)
rtClosTrans R nil q = q
rtClosTrans R (cons y r p) q = cons y r (rtClosTrans R p q)


{--
  the goal is to give a precise mathematical model
  of computations/programs

  operational semantics is nicely represented in Agda!

  similar representations are done in HOL, Lean, ...
  but not with explicit proof representations (interaction using tactics instead, only seeing goals)



  This line of research is quite old: a first example of a proof of a (very simple)
  compiler was carried out on papers in 1967 by McCarthy-Painter
  see http://jmc.stanford.edu/articles/mcpain/mcpain.pdf

 "This paper contains a proof of the correctness of a simple compiling algorithm
 for compiling arithmetic expressions into machine language.
 The definition of correctness, the formalism used to express the description
 of source language, object language and compiler, and the methods of proof are
 all intended to serve as prototypes for the more complicated task of proving the
 correctness of usable compilers. The ultimate goal, as outlined in references
 [1], [2], [3] and [4] is to make it possible to use a computer to check proofs that
 compilers are correct.
 The concepts of abstract syntax, state vector, the use of an interpreter
 for defining the semantics of a programming language, and the definition of
 correctness of a compiler are all the same as in [3]. The present paper, however,
 is the first in which the correctness of a compiler is proved."

  Abstract syntax: they represent the syntax of the programming language as a data type


  In 1972, this was formalised by Milner and Weyhrauch

  concrete applications: software correctness
      compiler
      C compiler    Xavier Leroy CompCert
      avionics to be sure about optimisations     see  https://www.absint.com/tum_fsd.htm

      CakeML   project    compiler for ML programming language
      developped here at Chalmers

  I will present a simplified version of what they did in Agda

--}

-- abstract syntax of the language

data Nat : Set where
 zero : Nat
 suc  : Nat -> Nat

add : Nat -> Nat -> Nat
add n zero    = n
add n (suc m) = suc (add n m)

one : Nat
one = suc zero

two : Nat
two = suc one

data exp : Set where
 Const : Nat -> exp
 Add : exp -> exp -> exp

-- we can define the -denotational- semantics in Agda

val : exp -> Nat
val (Const n) = n
val (Add e0 e1)  = add (val e0) (val e1)

-- a compiled program is a list of atomic commands

data Cmds : Set where
 LOAD : Nat -> Cmds -> Cmds
 ADD  : Cmds -> Cmds
 HALT : Cmds

compile : exp -> Cmds -> Cmds
compile (Const n) cd = LOAD n cd
compile (Add e0 e1) cd = compile e0 (compile e1 (ADD cd))

exExp1 : exp
exExp1 = Add (Const zero) (Add (Const zero) (Const zero))

exExp2 : exp
exExp2 = Add (Add (Const two) (Const two)) (Add (Const one) (Const two))

exComp : Cmds
exComp = compile exExp1 HALT

ex1Comp : Cmds
ex1Comp = compile exExp2 HALT

data _×_ (A B : Set) : Set where
 pair : A -> B -> A × B

-- we use a list for representing a stack

data list (A : Set) : Set where
 nil   : list A
 cons  : A -> list A -> list A

_·_ : {A : Set} -> A -> list A -> list A
x · xs = cons x xs

infixr 30 _·_

state : Set
state = Cmds × list Nat 

_,_ : {A B : Set} -> A -> B -> A × B
a , b = pair a b


data _↦_ : state -> state -> Set where
 ->A : {cd : Cmds} -> {n0 n1 : Nat} -> {s : list Nat} ->
            (ADD cd , n1 · (n0 · s)) ↦ (cd , (add n0 n1) · s)
            
 ->L : {cd : Cmds} -> {n : Nat} -> {S : list Nat} ->
            (LOAD n cd , S) ↦ (cd , n · S)


_↦∗_ : state -> state -> Set
e ↦∗ e' = rtClos _↦_ e e'

infixr 2 _using<_>_

_using<_>_ : ∀ (x : state) {y z : state }
    → x  ↦∗ y
    → y  ↦∗ z
      -----
    → x  ↦∗ z
x using< p > q  =  rtClosTrans _↦_ p q

_stop : (x : state ) -> x  ↦∗ x
_stop x = nil

oneStep : {x y : state } -> x ↦ y ->  x  ↦∗ y
oneStep {x} {y} p = cons y p nil

thmComp : (e : exp) -> (cd : Cmds) -> (S : list Nat) -> (compile e cd , S) ↦∗ (cd , (val e) · S)
thmComp (Const n) cd S = oneStep ->L
thmComp (Add e0 e1) cd S =
    (compile (Add e0 e1) cd , S)

--  using<  nil >

--    (compile e0 (compile e1 (ADD cd)) , S)

  using< thmComp e0 (compile e1 (ADD cd)) S >

    (compile e1 (ADD cd) , cons (val e0) S)

  using< thmComp e1 (ADD cd) ((val e0) · S) >

    (ADD cd , (val e1) · ((val e0) · S))

  using< oneStep ->A >

    (cd , (val (Add e0 e1)) · S)

  stop

-- the corollary states the correctness of compilation

corComp : (e : exp) -> (compile e HALT , nil) ↦∗ (HALT , cons (val e) nil)
corComp e = thmComp e HALT nil

