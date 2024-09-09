module Lecture2 where

{-

 My lectures

 Week 1: more about Agda as a programming language
         Propositions as Types, Proofs as Programs

 Week 2: operational semantics (in Agda)
         safety = progress + preservation
         how to prove correctness of a compiler

 Week 3: lambda calculus
         substitution and operational semantics
         how to evaluate lambda terms, closure, abstract evaluation machine

 All proofs will be done in Agda

 Agda itself is based on typed lambda calculus!


 About some goals for a system like Agda

 Developping correct programs:  talk of Conal Eliott

 https://www.youtube.com/watch?v=k6rY5Mvx84E&t=3693s&ab_channel=OST%E2%80%93OstschweizerFachhochschule

 Developing correct compilers: talk of Sandrine Blazy

 https://gdr-gpl.cnrs.fr/sites/default/files/documentsGPL/JourneesNationales/GPL2023/Blazy.pdf

  "As of early 2011, the under-development version of CompCert is the only compiler we have tested for which Csmith cannot
  find wrong-code errors. This is not for lack of trying: we have devoted about six CPU-years to the task. The apparent
  unbreakability of CompCert supports a strong argument that developing compiler optimizations within a proof framework,
  where safety checks are explicit and machine-checked, has tangible benefits for compiler users."


 Cf. also work on CakeML https://cakeml.org/

 About history of type theory, the paper of Martin-Löf

 Constructive Mathematics and Computer Programming

 available at https://github.com/michaelt/martin-lof

 is very relevant (almost everything is now in Agda, -except- the treatment of equality)

 


-}



{-

 First week

 -more intro to programming in Agda

   In these lectures
   Agda = functional programming languages λ-calculus + data types + pattern-matching
          with dependent types

 -All programs should terminate in Agda

 -A type of types Set

 -Types can be used to represent propositions: Haskell Curry's discovery

 -History and timeline:

     Frege 1872, laws for quantification, axioms for propositional and predicate logic
     Gentzen 1930, Natural Deduction discovery of special status of the law of Excluded Middle
     Curry 1930, correspondance between combinators S and K and the axioms of Frege
     Kolmogorov 1930, propositions as problems, also special status of the law of Excluded Middle
     de Bruijn, Howard, Martin-Löf 60s, correspondance between types and propositions
     de Bruijn 60s, system AUTOMATH, dependent type theory, quantifier as dependent types
     Martin-Löf 70s, Constructive Mathematics and Computer Programming
     80s, first implementations of systems like Agda
     90s, contrary to systems with tactics, direct representation of proofs in a programming language
     2005, Agda2
     2008, non trivial C compiler developped correctly in type theory (CompCert)
     2010, Voevodsky, type theory as a language for expressing homotopy theory
     2020, non trivial mathematics developped in Lean
     
 -Agda vs Haskell, Agda vs systems like Lean or Coq or Idris

 -Why use Agda? See the talk of Conal Eliott cited above

 -Agda "good" representation of natural deduction
  Test the example A -> C, B -> D, A ∨ B ⊢ C ∨ D on chatgpt first with natural deduction and then with Agda
  Or the example not a, a ∨ b |- b 


-}

-- This lecture: basic data types and defining functions and values
-- dependent product types and type of types
-- implicit arguments


-- Natural numbers and Boolean have built in facility but they can be introduced as data type

data Bool : Set where
 true  : Bool
 false : Bool

data Nat : Set where
 zero : Nat
 suc  : Nat -> Nat  

one : Nat
one = suc zero

two : Nat
two = suc one

-- We can also use the type Set of "all" types to define types with parameters

-- in some sense simpler than Haskell

data list (A : Set) : Set where
  nil : list A
  cons : A -> list A -> list A

tlist : (A : Set) -> Set    -- Set -> Set       
tlist = list

-- Another example of a types with parameters

data Tree (A : Set) : Set where
 br : Tree A -> Tree A -> Tree A
 leaf : A -> Tree A

exTree : Tree Bool
exTree = br (leaf true) (leaf false)

-- How to define a function?
-- by pattern-matching/case analysis

-- compare with what is a function in set theory: a functional relation
-- which may not be computable
-- example: f n = 0 iff there is no consecutive n 7 in the decimal development of π
--          and f n = 1 otherwise
-- this is a function set theoretically; but it cannot be now represented as a program

pred : Nat -> Nat
pred zero = zero
pred (suc x) = x

rev : {A : Set} -> Tree A -> Tree A
rev (br t0 t1) = br (rev t1) (rev t0)
rev (leaf a) = leaf a

rev1 : (A : Set) -> Tree A -> Tree A
rev1 A (br t0 t1) = br (rev1 A t1) (rev1 A t0)
rev1 A (leaf a) = leaf a

-- we can evaluate an expression
-- exTree = br (leaf true) (leaf false)

testTree : Tree Bool
testTree = rev exTree         -- rev {Bool} exTree

-- use of dependent types
-- (x : A) -> B same as A -> B  if x not free in B

-- cons is "essentially" of type (A : Set) -> A -> list A -> list A

-- A is bound variable in this expression
-- simpler than Haskell?

tcons : {A : Set} -> A -> list A -> list A
tcons = cons

explicitcons : (A : Set) -> A -> list A -> list A
explicitcons A a as = cons a as

-- use {A : Set} and not (A : Set) to indicate that the argument A is -implicit-

{-

id : {A : Set} -> A -> A
id {A} x = x

-}

variable
 A : Set

id : A -> A
id x  = x


exNat1 : Nat
exNat1 = id one -- id {Nat} one

-- like Haskell polymorphism

-- in Agda all functions should be total functions

{-

loop : Nat
loop = loop



bar : Nat -> Nat
bar zero = zero
bar (suc x) = bar (suc x)

-}


-- See the file nontermination.agda for counter-examples


-- How to ensure that all functions are total?

-- PRIMITIVE RECURSION
-- ITERATION

-- on Bool

boolrec : {X : Set} -> X -> X -> Bool -> X
boolrec {X} a0 a1 true = a0
boolrec {X} a0 a1 false = a1

-- this function is actually not recursive!
-- this is: if then else

-- on Nat

-- primitive recursion
natrec : {A : Set} -> A -> (Nat -> A -> A) -> Nat ->  A
natrec {A} base next zero = base
natrec {A} base next (suc n) = next n (natrec base next n)

-- iteration
natit  : {X : Set} -> X -> (X -> X) -> Nat ->  X
natit base next zero = base
natit base next (suc n) = next (natit base next n)

-- the idea of primitive recursion is quite old: Skolem ~1920

-- primitive recursion with higher functions goes back to Hilbert 1925



-- predecessor on Nat cannot be directly defined by iteration
-- but it can be defined by primitive recursion

-- primitive recursion

add : Nat -> Nat -> Nat
add n zero = n
add n (suc m) = suc (add n m)

-- how to define add with primitive recursion?
-- with iteration?

-- primitive recursive definition with parameter n

mult : Nat -> Nat -> Nat
mult n = f where
 f : Nat -> Nat
 f zero = zero
 f (suc m) = add n (f m)

--

zeroStrict : Nat -> Nat
zeroStrict zero = zero
zeroStrict (suc x) = zeroStrict x

-- in Haskell, this function is not the same as the constant function zeroF x = zero
-- in Agda, there is no way to make an observable distinction between zeroStrict and zeroF!
-- Agda is a functional programming language where all functions terminate

-- one can however define functions that -in practice- would take too long/too much memory to compute

-- Ackermann function
-- a function which is not "primitive recursive"
-- but it is primitive recursive if we allow functional parameters!

ack : Nat -> Nat -> Nat
ack zero m = suc m
ack (suc n) zero = ack n one
ack (suc n) (suc m) = ack n (ack (suc n) m)

-- the definition does not have the form    f zero = a    f (suc n) = g n (f n)
-- primitive recursive but with higher types parameters

-- how to rewrite iterate in a primitive recursive way??

-- so iterate f m is   f(f( ... (f one)... ))  where f is iterated m+1 times

Ack : Nat -> (Nat -> Nat)
Ack zero = suc
Ack (suc n) = natit one (Ack n)

-- this is primitive recursive  but with a simple form   f zero = a    f (suc n) = g (f n)
-- so  f n is   g (g...(g a)...)

-- Ack n   is  iterate (iterate ... (iterate suc) ...)  
-- where iterate = natit one

-- intuitively Ackermann grows quickly since we iterate an "iteration"

minus : Nat -> Nat -> Nat
minus zero m = zero
minus (suc n) zero = suc n
minus (suc n) (suc m) = minus n m

-- this also is not pritimive recursive

itM : Nat -> (Nat -> Nat) -> Nat -> Nat
itM n f zero = suc n
itM n f (suc m) = f m

constZ : Nat -> Nat
constZ x = zero

Minus : Nat -> (Nat -> Nat)
Minus zero = constZ
Minus (suc n) = itM n (Minus n) 

-- Minus is primitive recursive
-- minus is not but it is accepted by Agda since the recursive call
-- is formally smaller

-- how to prove that minus and Minus are the same functions??

-- on list
{-
listrec : {A X : Set} -> X -> (A -> list A -> X -> X) -> list A -> X
listrec {A} {X} base next nil = base
listrec {A} {X} base next (cons x xs) = next x xs (listrec base next xs)
-}
-- maybe clearer

listrec : {A X : Set} -> X -> (A -> list A -> X -> X) -> list A -> X
listrec {A} {X} base next = foo
 where foo : list A -> X
       foo nil = base
       foo (cons x xs) = next x xs (foo xs)


listit : {A X : Set} -> X -> (A -> X -> X) -> list A -> X
listit {A} {X} base next nil = base
listit {A} {X} base next (cons x xs) = next x (listit base next xs)

-- this is called foldr in Haskell and "reduce" in some other functional language


-- example: define map on list
-- map : {A B : Set} -> (A -> B) -> list A -> list B

map : {A B : Set} -> (A -> B) -> list A -> list B
map f = listit nil (λ a -> cons (f a))

-- on Trees?

-- some functions

odd : Nat -> Bool
odd zero = false
odd (suc zero) = true
odd (suc (suc n)) = odd n

even : Nat -> Bool      
even zero = true
even (suc zero) = false
even (suc (suc n)) = even n

not : Bool -> Bool
not true = false
not false = true

and : Bool -> Bool -> Bool
and true true = true
and true false = false
and false y = false

equiv : Bool -> Bool -> Bool
equiv true y = y
equiv false y = not y

-- can we use Bool for representing propositions?

-- this is what is done in a system like HOL

-- forall : (Nat -> Bool) -> Bool cannot be a total function and represented in a programming language!!!

-- forall f is not computable, intuitively because we have to compute f 0, f 1, f 2, ... and the computation never stops

-- On the other hand, it is possible to define forall on a finite type, e.g. on Bool


forallB :  (Bool -> Bool) -> Bool
forallB f =  and (f true) (f false)

-- the representation of logic will take another way, which might be quite surprising at first, where one
-- represents a proposition as an Agda type

{--

 This is "explained" by Kolmogorov view of a proposition: a proposition is like a problem 
and a proof of this proposition is a solution of this problem


 then a solution of the problem A -> B
 consists in reducing the problem B to the problem A
 i.e. a function    solution of A -> solution of B

 ⊥ should be a problem with no solution
 a solution ¬ A = A -> ⊥   is to show that A has no solution

 a : A        a is a solution of the problem A
              a is a proof of the proposition A 
              a is an element of type A

 This generalises to more connectives

proposition      type

P ⊃ Q            A → B   - Function type
P ∧ Q            A × B   - Cartesian Product - type of pairs
P ∨ Q            A + B   - Disjoint Union - type of tagged union
                         - "Either" in Haskell
⊤                Unit    - Unit type (has one element)
⊥                ∅       - Empty type
¬ P              A → ∅   - Negation as function into the empty type    

 This is quite nice

   -it reduces proof checking to type checking

   -it provides an explicit notation for proofs (that should be fundamental, but are 
   "hidden" or "meta" in usual presentation)

   -like all good analogy, it forces us to try to explore further the analogy and find corresponding notions
     e.g. what logical notion corresponds to use of monads?
          let, where corresponds to use of Lemmas
          recursive programs correspond to proofs by induction
          what logical notion corresponds to notion of fusion in functional programming
          what programming notion corresponds to proofs by contradiction?
          etc.

 In a way really surprising: for instance we do have one function ∅ -> A for
 any set A 
 In logic, we do have Ex Falso Quodlibet/the principle of Explosion

-}


