module Lecture4 where

open import Lecture2

{-

 We use the Deduction Theorem for an introduction to OPERATIONAL SEMANTICS

 How to reason about deduction systems given by some inference rules

 This is what is used for presenting the computation rules of a programming language

 In mathematics, the only induction principle is on natural numbers

 In computer science and logic, there are much more inductive notions: trees, lists, proof trees, ... and we want to do
 proofs by induction over these notions


 The deduction theorem tells us that in order to prove A => B from a list of hypotheses G
 it is enough to add A to the list G and then prove B from this extended list

 We need first to define what it means to prove a sentence from a list of hypotheses

    -either the sentence is in the list
    -or the sentence is an instance of an axiom (here two axioms S and K)
    -or the sentence can be deduced from modus-ponens: we have deduced A => B and we have deduced A
    and we deduce B by modus-ponens

 This definition is inductive: we define G |- A read "A is deduced from the hypotheses G" by induction

 We represent a proof that G |- A as a -tree-
 Traditionally, such a proof is represented as a sequence

     A1, ..., An

 with An = A and each Ai is either an instance of an axiom or is such that we have Aj = Ak => Ai for some k < i and j < i

 The representation as a deduction tree is much more natural
 
      G |- A => B      G |- A
      -----------------------
            G |- B




 We show then -by induction- that if G, A |- B then we have G |- A => B

 We have a lot of cases

 One key case is that we have G, A |- C => B and G, A |- C
 By -induction- we have G |- A => (C => B) and G |- A => C
 We want G |- A => B
 This is exactly where the axiom S plays a role




-}

{-

 One important idea in such a representation as data types is the notion of -abstract syntax-


  "It has long been recognised that the essential syntactical structure of programming languages is not that given by their concrete or
   surface syntax—as expressed, say, by a language description in BNF oriented to parsing (there the parse trees contain much information useless for
   language processing). Rather, the deep structure of a phrase should reflect its semantic import.
   McCarthy coined the term abstract syntax for such structure, which is typically given as a tree with its top node labelled by the main semantic constituent,
   or, equivalently, by a term of first-order logic. Abstract syntax has both synthetic and analytic aspects: the former concerns the constructors needed
   to form phrases, the latter the destructors (predicates and selectors) needed to take them apart. Burstall contributed structural recursion—a generalised
   form of primitive recursion—to analytic syntax, with an associated principle of structural induction."
   
 from the paper "Abstract syntax and variable binding" Fiore, Plotkin, Turi

 See also the original paper of McCarthy "Towards a mathematical science of computation", 1963

-}

{-

 A. Turing     1944 The Reform of Mathematical Notation and Phraseology

 "The deduction theorem should therefore be as well known as integration by parts"

 See Wikipedia Deduction Theorem

-}


-- Form is the data type of "formulae", built only from atoms and implication
data Form : Set  where
 imply : Form -> Form -> Form
 atom : Nat -> Form

-- context is the type of list of formulae
-- the terminology "context" comes from the system AUTOMATH
context : Set
context = list Form

-- nicer notation for implication
infixr 10 _=>_
_=>_ : Form -> Form -> Form
X => Y = imply X Y

-- nicer notation for contexts
infixr 10 _,_
_,_ : context -> Form -> context
G , X = cons X G

-- a formulae is in a context
data isIn : context -> Form -> Set where
 zero : {X : Form} -> {G : context} ->
             isIn (G , X) X
 suc : {X Y : Form} -> {G : context} ->
             isIn G X ->
             isIn (G , Y) X 

-- Example of a proof tree in Agda
-- Created live during the lecture
proof_tree : {X Y : Form} → isIn ((nil , X) , Y) X
proof_tree {X} {Y} = suc {X} {Y} {nil , X} (zero {X} {nil})

infixr 6 _⊢_


-- defines when a formula is a consequence of a list of hypotheses
data _⊢_ : context -> Form -> Set where
 var : {X : Form} -> {G : context} -> isIn G X -> G ⊢ X
 axK : {X Y : Form} -> {G : context} -> G ⊢ X => (Y => X)
 axS : {X Y Z : Form} -> {G : context} -> G ⊢ (X => (Y => Z)) => ((X => Y) => (X => Z))
 mp : {Y X : Form} -> {G : context} ->
      G ⊢ Y => X ->
      G ⊢ Y ->
      -------------
      G ⊢ X
{-
    axI == axiom I == i combinator (combinatory logic) == id (haskell)
    axK == axiom K == k combinator (combinatory logic) == const (haskell)
    axS == axiom S == s combinator (combinatory logic) == (<*>) (haskell)
    mp == modus ponens (logic) == ($) (function application)
-}

dedlem1 : {G : context} -> {X : Form} -> G ⊢ X => X
dedlem1 {G} {X} = mp (mp axS axK) (axK {X} {X})

dedlem2 : {G : context} -> {X Y : Form} -> G ⊢ Y -> G ⊢ X => Y
dedlem2 d = mp axK d
--  dedlem2 {G} {X} d = mp (axK {X} {Y} {G}) d

dedlem3 : {G : context} -> {X Y : Form} -> isIn (G , X) Y -> G ⊢ X => Y
dedlem3 zero = dedlem1
dedlem3 (suc x) = dedlem2 (var x)      -- x is a proof that isIn G Y
-- x : IsIN G X
-- dedlem2: G ⊢ Y -> G ⊢ X => Y

dedthm : {G : context} -> {X Y : Form} -> G , X ⊢ Y -> G ⊢ X => Y
dedthm (var h) = dedlem3 h
dedthm axK = mp axK axK
dedthm axS = mp axK axS
dedthm (mp h0 h1) = mp (mp axS (dedthm h0)) (dedthm h1)

{-
dedthm (var h) = dedlem3 h
dedthm axK = mp axK axK -- dedlem2 axK
dedthm axS = mp axK axS -- dedlem2 axS
dedthm (mp h h1) = mp (mp axS (dedthm h)) (dedthm h1)
-}

dedex2 : {G : context} -> {X Y Z : Form} -> G ⊢ (X => Y) => ((Y => Z) => (X => Z))
dedex2 {G} {X} {Y} {Z} = dedthm (dedthm (dedthm (mp (var (suc zero)) (mp (var (suc (suc zero))) (var zero)))))

dedex3 : {G : context} -> {X : Form} -> G ⊢ X => X
dedex3 {G} {X} = dedthm (var zero)

dedex4 : {G : context} -> {X Y : Form} -> G ⊢ X => (Y => X)
dedex4 {G} {X} {Y} = dedthm (dedthm (var (suc zero)))

dedex5 : {G : context} -> {X Y Z : Form} -> G ⊢ (X => (Y => Z)) => (Y => (X => Z))
dedex5 {G} {X} {Y} =
 dedthm (dedthm (dedthm (mp (mp (var (suc (suc zero))) (var zero)) (var (suc zero)))))

K : {A B : Set} -> A -> B -> A
K a b = a

S : {A B C : Set} -> (A -> B -> C) -> (A -> B) -> A -> C
S f g a = f a (g a)

test : {A B : Set} -> A -> B -> A
test {A} {B} = S (K K) (S K (K {A} {A}))

-- Here is another presentation of logic, which may seem more natural, where the deduction theorem is "built-in"

-- natural deduction

infixr 6 _⊢N_

--lambda calculus
data _⊢N_ : context -> Form -> Set where
 var : {X : Form} -> {G : context} -> isIn G X -> G ⊢N X
 lam : {X Y : Form} -> {G : context} -> G , X ⊢N Y -> G ⊢N X => Y
 app : {Y X : Form} -> {G : context} -> G ⊢N Y => X -> G ⊢N Y -> G ⊢N X

-- we show that this new notion of deduction is equivalent to the previous one


thm1 : {G : context} -> {X : Form} -> G ⊢N X -> G ⊢ X
thm1 (var x) = var x
thm1 (lam h) = dedthm (thm1 h)
thm1 (app h h1) = mp (thm1 h) (thm1 h1)

thm2 : {G : context} -> {X : Form} -> G ⊢ X -> G ⊢N X
thm2 (var x) = var x
thm2 axK = lam (lam (var (suc zero)))
thm2 axS = lam (lam (lam (app (app (var (suc (suc zero))) (var zero)) (app (var (suc zero)) (var zero)))))
thm2 (mp h h1) = app (thm2 h) (thm2 h1)

exthm1 : {G : context} -> {X : Form} -> G ⊢ X => X
exthm1 {G} {X} = thm1 (lam (var zero))

{-

 equality is one of the most subtle notion in logic!

 Leibniz's principle of identity of indiscernables, Discourse on Metaphysics, 1686

 Some recent contributions on this mysterious notion:

        Per Martin-Löf 1973: addition of ∨, ⊥, and equality/identity type

        Vladimir Voevodsky 2005  towards a more satisfactory representation of equality

 Jesper Cockx 2017 did important work to understand how to use pattern-matching notation for representing these ideas

-}

-- constructors correspond to introduction rule/basic inference rules

-- data Bool : Set where true false : Bool
-- data Nat : Set where zero : Nat   suc : Nat -> Nat
-- data _∧_ (A B : Set) : Set where pair : A -> B -> A ∧ B

{-

 introduction rule for ∧

      A     B 
     ---------
       A ∧ B


 introduction for ≡

      --------
       x ≡ x

-}

data _≡_ {A : Set} (x : A) : (y : A) → Set where
 refl : x ≡ x

Id : {A : Set} -> (x : A) -> (y : A) -> Set
Id = _≡_

-- Id has only one constructor  refl : Id x x

-- introduction rule: how to prove something of the form a ≡ b
-- elimination: how do we prove something using an hypothesis a ≡ b

infix 4 _≡_

cong : {A B : Set} -> (f : A -> B) -> {x y : A} -> x ≡ y -> f x ≡ f y
-- cong {A} {B} f {x} {.x} refl = refl
-- cong {A} {B} f {x} {.x} refl = refl
-- cong {A} {B} f {.y} {y} refl = refl
cong _ refl = refl

IdisTransitive : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
IdisTransitive refl q = q

{-- what is going on?

 proof by case analysis

       a ≡ a1
 
 what are the possible way to prove this?

     -----------
       a ≡ a

 in this case the proof is trivial since what I have
 to prove is f a ≡ f a
 which is direct by reflexivity

 All this is nicely summarized by the definition

 cong f refl = refl

  cong {A} {B} f {x} {y} p = ?

 when Agda looks at the possible shape of p, Agda recognizes that it has
 to be of the form   refl 

 but then we should have  x ≡ x    convertible to    x ≡ y

 so we should have x, y convertible

 Agda records this as 

  cong {A} {B} f {x} {.x} refl = ?

 or

  cong {A} {B} f {.y} {y} refl = ?

-}

leibniz : {A : Set} {x y : A} -> (P : A -> Set) -> P x -> x ≡ y -> P y
leibniz {A} {x} {.x} P p refl = p

{-

 The principle that if x is identical with y, then every property that x has y has, 
 and vice versa. This is sometimes known as Leibniz's law.

-}


convLeibniz : {A : Set} {x y : A} -> ((P : A -> Set) -> P x -> P y) -> x ≡ y
convLeibniz {A} {x} {y} h = h x≡ refl  -- h : (P : A -> Set) -> P x -> P y
  where x≡ : A -> Set
        x≡ z =   x ≡ z

-- a nice exercise is to prove the following   in Bertrand Russell 1903
--  {A : Set} {x y : A} ->
--            ((P : A -> Set) -> P x -> P y) ->
--            (P : A -> Set) -> P y -> P x


-- for proving something using refl
-- Agda has to recognize that two terms are convertivble

-- id : {A : Set} -> A -> A
-- id x = x

-- we then have that   id n   and n are convertible

{-

 One can show that all operations with ≡ are consequences of the following
 elimination rules

 elimId : {A : Set} {x : A} -> (C : (y : A) -> x ≡ y -> Set) -> C x refl ->
          (y : A) -> (p : x ≡ y) -> C y p
 elimId {A} {.y} C h y refl = h         
         
-}

symId : {A : Set} -> {a b : A} -> a ≡ b -> b ≡ a
symId refl = refl

--  here is an example which shows that case on identity proof is a subtle process

testId : {n m : Nat} -> add n m ≡ add m n -> add m n ≡ add n m
-- testId p = {!p!}   -- Agda cannot do a case analysis!!
testId = symId

-- id : {A : Set} -> A -> A
-- id x = x

lem-trivial1 : (n : Nat) -> id n ≡ n
lem-trivial1 n = refl

-- refl : id n ≡ n
-- refl : a ≡ b??
-- the normal form of id n is n

-- this is the case since Agda can recognize that id n reduces to n

{-
 I recall the definition of addition

 add : Nat -> Nat -> Nat
 add n zero = n
 add n (suc m) = suc (add n m)

 there is another definition of addition 

 In Peano arithmetic    it is expressed in predicate logic

 these laws   x + 0 = x and x + s y = s (x + y)    are axioms
 and we can prove  0 + x = x   by induction

-}

other-add : Nat -> Nat -> Nat
other-add zero m = m
other-add (suc n) m = suc (other-add n m)

lemTriv : (n : Nat) -> n ≡ add n zero
lemTriv n = refl

-- this does not work
-- lem : (n : Nat) -> n ≡ add zero n
-- lem n = refl

-- lem : (n : Nat) -> n ≡ other-add n zero
-- cannot be proved with refl!

-- add n zero = n
-- add n (suc m) = suc (add n m)

lemAddZ : (n : Nat) -> n ≡ add zero n
lemAddZ zero = refl
lemAddZ (suc n) = cong suc (lemAddZ n)

{-where lem1 : n ≡ add zero n
       lem1 = lemAddZ n
       lem2 : suc n ≡ suc (add zero n)  --  suc n ≡ add zero (suc n)
       lem2 = cong suc lem1
-}

-- cong : {A B : Set} -> (f : A -> B) -> {x y : A} -> x ≡ y -> f x ≡ f y

-- this is a proof by induction
-- base case   0 ≡ 0 + 0
-- induction case   n ≡ 0 + n   --->   suc n ≡ 0 + succ n

-- add n zero = n
-- add n (suc m) = suc (add n m)

lemAddS : (n m : Nat) -> suc (add n m) ≡ add (suc n) m
lemAddS n zero = refl
lemAddS n (suc m) = cong suc (lemAddS n m)

-- in the case m = zero      succ (add n zero) = suc n  not ≡
--                           add (suc n) zero  = suc n

-- how to present proofs by equality reasoning
-- we want to represent a chain of equality
-- x1 ≡ x2 ≡ ... ≡ xn
-- justifying at each steps why each equality holds

-- this is exactly what transId is doing

-- note that we can use freely -> or →


transId : {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
transId refl refl = refl

-- the next operation is a nice example of mixfix operator
-- see https://www.cse.chalmers.se/~nad/publications/danielsson-norell-mixfix.pdf

infixr 2 _by<_>_

_by<_>_ : {A : Set} -> (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
x by< x≡y > y≡z  =  transId x≡y y≡z

-- I start from x
-- I use that I have a proof of x≡y
-- I use a proof of y≡z and I conclude x ≡ z

_□ : {A : Set} -> (x : A) -> x ≡ x    -- \Box  for □
_□ {A} x = refl

infix 3 _□

_+_ : Nat -> Nat -> Nat
_+_ = add

otherproofofAddS : (n m : Nat) -> suc (n + m) ≡ suc n + m
otherproofofAddS n zero = refl

otherproofofAddS n (suc m) =  
    suc (n + suc m)     by< refl >
    suc (suc (n + m))   by< {!!} {!!} >
    suc (suc n + m)     by< {! !} >
    suc n + suc m       □

{-
comAdd : (n m : Nat) -> n + m ≡ m + n
comAdd n zero = lemAddZ n
comAdd n (suc m) =
      n + (suc m)    by< refl >
      suc (n + m)    by< cong suc (comAdd n m) >
      suc (m + n)    by< lemAddS m n >  -- lemAddS m n : suc (m + n) ≡ (suc m) + n
      (suc m) + n    □

{-  compare with 
testAdd : (n m : Nat) -> add n m ≡ add m n
testAdd n zero = lemAddZ n
testAdd n (suc m) = 



  transId 
    (cong suc (testAdd n m)) 
    (lemAddS m n)

or
p
testAdd : (n m : Nat) -> add n m ≡ add m n
testAdd n zero = lemAddZ n
testAdd n (suc m) = 
  transId 
    refl
    (transId 
      (cong suc (testAdd n m)) 
      (lemAddS m n))

-}

{-
 this style of interacting with a system should be compared
 with reasoning by tactics
 where we don't have a concrete presentation of the proof

 Isabelle, Lean, Idris, ... 

 see for instance 

  https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/

 for how to do proofs by induction with tactics

-}

add-is-associative : (n m p : Nat) -> n + (m + p) ≡ (n + m) + p
add-is-associative n m zero = refl
add-is-associative n m (suc p) =
 cong suc (add-is-associative n m p)

+_is_associative : (n m p : Nat) -> (n + m) + p ≡ n + (m + p)

+_is_associative n m zero = 
    (n + m) + zero
  by< refl >
    n + m
  by< refl >
    n + (m + zero)
  □

+_is_associative n m (suc x) =
    (n + m) + (suc x)
  by< refl >
    suc ((n + m) + x)
  by< cong suc (+_is_associative n m x) >
    suc (n + (m + x))
  by< refl >
    n + suc (m + x)
  by< refl >
    n + (m + suc x)
  □

-}



{-

 Function extensionality is not provable

 funExt : {A B : Set} -> {f g : A -> B} -> ((x : A) -> f x ≡ g x) -> f ≡ g

 Two functions are equal if they are pointwise equal

 It is built-in in systems like HOL

 In Set Theory, extensionality is the first axiom: two sets are equal if they have the same elements

-}




{-
axK : {A : Set} -> {x : A} -> (p : x ≡ x) -> p ≡ refl
axK refl = refl
-}

----- Stuff below was added during lecture 5 -----

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

¬ : Set → Set
¬ A = A → ⊥

elim-⊥ : {A : Set} → ⊥ → A
elim-⊥ ()

isTrue : Bool → Set
isTrue true = ⊤
isTrue false = ⊥

BooltoSet1 : (b : Bool) → isTrue b → b ≡ true
BooltoSet1 true x = refl
BooltoSet1 false = elim-⊥

BooltoSet2 : (b : Bool) → b ≡ true → isTrue b
BooltoSet2 true x = tt
BooltoSet2 false h = lem2 lem3
  where
    lem : true ≡ false
    lem = symId h
    lem1 : isTrue true
    lem1 = tt
    lem2 : (isTrue false) → ⊥
    lem2 = λ z → z
    lem3 : isTrue false
    lem3 = leibniz {x = true} {y = false} isTrue lem1 (symId h)

data _∨_ : (A B : Set) → Set where
  inl : {A B : Set} → A → A ∨ B
  inr : {A B : Set} → B → A ∨ B
