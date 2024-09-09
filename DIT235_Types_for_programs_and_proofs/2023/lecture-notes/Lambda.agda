module Lambda where

{-
   this lecture corresponds to chapters 5 and 6 in Pierce's book
   chapter 5 untyped lambda calculus
   chapter 6 de Bruijn representation

   however I will assume that you are all familiar already with
   lambda-calculus (used in Haskell and Agda!) and concentrate
   on a formal representation in Agda using de Bruijn's representation of
   lambda terms

   untyped lambda-calculus captures the essence of functional programming

   to do the theory of lambda-calculus in an elegant way is still an active field of research!

   id : {A : Set} → A → A
   id x = x
   id {A} = λ x -> x

   λ-calculus was invented by Alonzo Church 1930
   he was inspired by Frege and Principia Mathematica of Whithehead and Russell
   first version of Higher-Order Logic

   There we define the predicate
        x^ psi(x)
        λ x psi(x)
    this represents the predicate of x satisfying the property psi

    so we also have   psi = x^ psi(x)

                     _ is even

    for instance
       (x^   x is even) (2)    means   2 is even
       (x^   x ≡ 2) (2)        means   2 ≡ 2
       (x^   x ≡ 2) (3)        means   3 ≡ 2

     λ x   x ≡ 2          Church's notation
     λ x  ->  x ≡ 2       Agda notation

    Russell's paradox was expressed in the form

     R =  x^ ¬ (x x)
     R R iff   ¬ (R R)

    i.e. the predicate of all predicates that do not satisfy itself

       R is a fixpoint for ¬
       This can been generalised    delta f = λ x f (x x) then Y f = delta f (delta f) satisfies Y f = f (Y f)

       A similar idea is used in Gödel's incompletenss proof
              G n m = the formula phi(x) coded by n is such that phi(m) is not provable
              then psi(x) = G x x has a code n0 and G n0 n0 states that G n0 n0 is not provable



    x^ P(x)   became   λ x P(x)

   Church used this as a programming language!!
   encode natural numbers and booleans; this original idea can be traced back to Wittgenstein 1921

   zero is encoded as  λ f λ x   x
   one  is encoded as  λ f λ x  f x
   two  is encoded as  λ f λ x  f (f x)
   and so on

   true is encoded as    λ x0 λ x1   x0
   false  is encoded as  λ x0 λ x1   x1

    if b then x0 else x1 is then encoded as   (b x0) x1

    for b = λ x0 λ x1  x0          (b x0 x1)  is x0
    for b = λ x0 λ x1  x1          (b x0 x1)  is x1

   we can encode addition

   λ n λ m λ f λ x    n f (m f x)

   multiplication

   λ n λ m λ f λ x    n (m f) x

   exponentiation

   λ n λ m λ f λ x    n m f x

   encoding predecessor function??
   solved by Kleene

   then realized that more and more functions could be encoded
   Church conjectured (just before Turing) that any computable functions can be encoded as a λ term

   This is known as Church's thesis
   this is like an axiom about computable functions
   so far nobody has found an example of an algorithm which is not
   representable by a Turing machine/lambda term

   other models of computation: actor model     

            Note that SCHEME (a version of LISP with a correct treatment of bound variables)
            SCHEME was introduced as a simplification of the actor model

   a little later, Turing was able to show formally that a function is
   representable by a Turing machine iff it can be encoded in λ-calculus

   λ-calculus was formulated before Turing machine

   we start the theory of untyped λ-calculus
   what is really subtle to define is the substitution operation

        note that the subsitution operation is a crucial component in Gödel's proof of incompletness


   informal     t   :=    x   |   t t     |    λ x t
     either a variable x
     or an application t u          mathematical notation t(u)
     or an abstraction λ x t        mathematical notation x ↦ t


   λ x x    should be the same  as   λ y y


 If we are not careful, we have the problem of "capture" of variables

 t = λxλy x y           intuitively t takes a function and does an eta-expansion
 u = y

 t u =  (λxλy x y) y  ->   λy (y y)    <--- this is not correct

 we should have

 t u =  (λxλz x z) y  ->   λz (y z)    <--- this is correct


 This problem with capture of variables/bound variable is something 
 relatively recent in mathematics

 It occured first in Leibnitz' notation for integrals

     ∫ f(x) dx             x  is bound

     ∫ f(z) dz             x  is bound

     ∫ (x² + xy) dx     we cannot rename y by x

     ∫ (z² + zy) dz     we rename x by z

     ∫ (z² + zx) dz     and now we can do the substitution y by x

 In logic, it occured in Frege's work 1879  who was the first to formulate
 the rule

      we have   A -> ∀x B(x)
      if        A -> B(x)
      -and-     x is not free in A

 This rule is actually -very- surprising, since we can capture the rule
 of quantification over any collection, even infinite, in a finite way!

 For stating this rule precisely, we need to be precise about the rules
 of free and bound variables

 This question has became important if we want to program computers to check
 mathematical proofs

 E.g. one early version for HOL light which has a very simple program to 
 check proofs in HOL had precisely a problem with capture of variables

 Same problem with implementation of the first system with dependent types AUTOMATH

 Even great mathematicians, such as Hilbert or Turing, made mistakes
 about substitutions and capture of variables!


   representation of variable?
   how do we treat variable in a compiler
   lexical analysis: check that a given variable has indeed been declared
   replace the variable by a number which is the distance to its declaration

   the number is the "static distance" which represents
   the number of variable declarations between a variable reference
   and its declaration

   λ x λ y x (x y)

   λ λ one (one zero)

   λ x λ y x (x (z y))    if we try to "compile" this with de Bruijn index
   λ λ one (one (z y))    lexical mistake   z has not been declared!

-}

data _≡_ {A : Set} (a : A) : A -> Set where
 refl : a ≡ a

infix 4 _≡_

symId : {A : Set} -> {a b : A} -> a ≡ b -> b ≡ a
symId refl = refl

transId : {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
transId refl refl = refl

cong : {A B : Set} -> (f : A -> B) -> {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl


infixr 2 _=<_>_

_=<_>_ : {A : Set} -> (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
x =< x≡y > y≡z  =  transId x≡y y≡z

-- I start from x
-- I use that I have a proof of x≡y
-- I use a proof of y≡z and I conclude x ≡ z

_□ : {A : Set} -> (x : A) -> x ≡ x    -- \Box  for □
_□ {A} x = refl

infix 3 _□

postulate funExt : {A : Set} {B : Set} {f g : A → B}  -> 
           ((x : A) → f x ≡ g x) →
           ---------------------
                 f ≡ g

_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
_∘_ g f x = g (f x)


-- the categorical laws are verified, thanks to βη-conversion

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → (x : A) → f x ≡ g x

cong-app refl x = refl

cong2 : {A B C : Set} (g : A -> B -> C) {x z : A} {y t : B} -> 
         x ≡ z ->          y ≡ t ->
         --------------------------
              g x y ≡ g z t
cong2 g refl refl = refl



-- untyped lambda-calculus

-- Think of X as the set of free variables

data Maybe (X : Set) : Set where
 zero : Maybe X
 suc : X -> Maybe X

-- nested data type

-- Form a monad
data Term (X : Set) : Set where
 var : X -> Term X
 lam : Term (Maybe X) -> Term X
 app : Term X -> Term X -> Term X

-- from Bird and Paterson  "de Bruijn notation as a nested data type"
-- compare with the corresponding rule for Nat
-- (X : Set) -> X -> (X -> X) -> Nat -> X


fsucT : (F : Set -> Set) ->
        ((X : Set) -> X -> F X) ->
        ((X : Set) -> F (Maybe X) -> F X) -> 
        ((X : Set) -> F X -> F X -> F X) ->
        {X : Set} -> Term X -> F X
        
fsucT F v l a {X} (var x)     = v X x
fsucT F v l a {X} (lam t)     = l X (fsucT F v l a t)
fsucT F v l a {X} (app t0 t1) = a X (fsucT F v l a t0)  (fsucT F v l a t1) 


-- some examples of lambda terms

-- this is exactly like de Bruijn notation

exId : {X : Set} -> Term X
exId {X} = lam (var zero)

exDelta : {X : Set} -> Term X
exDelta {X} = lam (app (var zero) (var zero))

exK : {X : Set} -> Term X
exK {X} = lam (lam (var (suc zero)))

exY : {X : Set} -> Term X
exY {X} = app exDelta exDelta

-- renaming of variables

liftM : {X Y : Set} -> (X -> Y) -> Maybe X -> Maybe Y
liftM f (suc x) = suc (f x)
liftM f zero     = zero

mapT : {X Y : Set} -> (X -> Y) -> Term X -> Term Y
mapT f (var x)     = var (f x)
mapT f (lam t)     = lam (mapT (liftM f) t)
mapT f (app t0 t1) = app (mapT f t0) (mapT f t1)

-- simultaneous substitution

-- suc : {X : Set} -> X -> Maybe X

up : {X : Set} -> Term X -> Term (Maybe X)
up = mapT suc

der :  {X Y : Set} -> (X -> Term Y) -> Maybe X -> Term (Maybe Y)
der f (suc x) = up (f x)
der f zero     = var zero

subst : {X Y : Set} -> (X -> Term Y) -> Term X -> Term Y
subst f (var x) = f x
subst {X} {Y} f (lam t) = lam (subst (der f) t)
subst f (app t0 t1) = app (subst f t0) (subst f t1)

id : {X : Set} -> X -> X
id {X} x = x

lemDvar : {X : Set} -> der var ≡ var
lemDvar {X} = funExt lem
 where lem : (u : Maybe X) -> der var u ≡ var u
       lem zero = refl
       lem (suc x) = refl


substVar : {X : Set} -> subst var ≡ id {Term X}

substVar {X} = funExt lem
 where lem : {X : Set} -> (t : Term X) -> subst var t ≡ t
       lem (var x) = refl
       lem (lam t) = cong lam rem where
         rem : subst (der var) t ≡ t
         rem = subst (der var) t =< cong-app (cong subst lemDvar) t >
               subst var t       =< lem t >
               t                 □
       lem (app t0 t1) = cong2 app (lem t0) (lem t1)

funLift : {X Y Z : Set} -> {g : Y -> Z} -> {f : X -> Y} -> liftM (g ∘ f) ≡ (liftM g) ∘ (liftM f)

funLift {X} {Y} {Z} {g} {f} = funExt lem where
 lem : (t : Maybe X) -> liftM (g ∘ f) t ≡ liftM g (liftM f t)
 lem zero = refl
 lem (suc x) = refl

funMapT : {X Y Z : Set} -> {g : Y -> Z} -> {f : X -> Y} -> mapT (g ∘ f) ≡ (mapT g) ∘ (mapT f)

funMapT = funExt lem where
 lem : {X Y Z : Set} -> {g : Y -> Z} -> {f : X -> Y} -> (t : Term X) -> mapT (g ∘ f) t ≡ mapT g (mapT f t)
 lem (var x) = refl
 lem {X} {Y} {Z} {g} {f} (lam t) = cong lam rem where
  rem :  mapT (liftM (g ∘ f)) t ≡ mapT (liftM g) (mapT (liftM f) t)
  rem =  mapT (liftM (g ∘ f)) t            =< cong-app (cong mapT funLift) t >
         mapT ((liftM g) ∘ (liftM f)) t    =< lem t >
         mapT (liftM g) (mapT (liftM f) t) □
 lem (app t0 t1) = cong2 app (lem t0) (lem t1)

lem0 : {X Y Z : Set} -> {g : Y -> Term Z} -> {f : X -> Y} -> der (g ∘ f) ≡ der g ∘ (liftM f)

lem0 = funExt lem
 where lem : {X Y Z : Set} -> {g : Y -> Term Z} -> {f : X -> Y} ->
                (x : Maybe X) → der (g ∘ f) x ≡ (der g ∘ liftM f) x
       lem zero = refl
       lem (suc x) = refl

substMap : {X Y Z : Set} -> {g : Y -> Term Z} -> {f : X -> Y} -> subst (g ∘ f) ≡ subst g ∘ (mapT f)

substMap = funExt lem
 where lem : {X Y Z : Set} -> {g : Y -> Term Z} -> {f : X -> Y} ->
                 (t : Term X) → subst (g ∘ f) t ≡ (subst g ∘ mapT f) t
       lem (var x) = refl
       lem {X} {Y} {Z} {g} {f} (lam t) = cong lam rem where
        rem : subst (der (g ∘ f)) t ≡ subst (der g) (mapT (liftM f) t)
        rem = subst (der (g ∘ f)) t                 =< cong-app (cong subst lem0) t >
              subst (der g ∘ (liftM f)) t           =< lem t >
              subst (der g) (mapT (liftM f) t)      □
       lem (app t0 t1) = cong2 app (lem t0) (lem t1)

lem1 : {X Y Z : Set} -> {f : X -> Term Y} -> {g : Y -> Z} ->
          (t : Term X) -> mapT g (subst f t) ≡ subst (mapT g ∘ f) t

lem1 {X} {Y} {Z} {f} {g} (var x) = refl
lem1 {X} {Y} {Z} {f} {g} (lam t) = cong lam rem where
  rem1 : {X Y Z : Set} -> {f : X -> Term Y} -> {g : Y -> Z} -> mapT (liftM g) ∘ (der f) ≡ der (mapT g ∘ f)
  rem1 {X} {Y} {Z} {f} {g} = funExt rem2 where
    rem2 : (x : Maybe X) → (mapT (liftM g) ∘ der f) x ≡ der (mapT g ∘ f) x
    rem2 zero = refl
    rem2 (suc x) =
       (mapT (liftM g) ∘ der f) (suc x)  =< refl >
       (mapT (liftM g) ∘ mapT suc) (f x) =< symId (cong-app funMapT (f x)) >
       mapT (liftM g ∘ suc) (f x)        =< refl >
       mapT (suc ∘ g) (f x)              =< cong-app funMapT (f x) >       
       mapT suc (mapT g (f x))           =< refl >
       der (mapT g ∘ f) (suc x)          □
  rem : mapT (liftM g) (subst (der f) t) ≡ subst (der (mapT g ∘ f)) t
  rem = mapT (liftM g) (subst (der f) t)      =< lem1 t >
        subst (mapT (liftM g) ∘ (der f)) t    =< cong-app (cong subst rem1) t >
        subst (der (mapT g ∘ f)) t            □
lem1 {X} {Y} {Z} {f} {g} (app t0 t1) = cong2 app (lem1 t0) (lem1 t1)

lemDer : {X Y Z : Set} -> {g : Y -> Term Z} -> {f : X -> Term Y} -> der (subst g ∘ f) ≡ subst (der g) ∘ (der f)

lemDer {X} {Y} {Z} {g} {f} = funExt lem where
 lem : (x : Maybe X) → der (subst g ∘ f) x ≡ (subst (der g) ∘ der f) x
 lem zero = refl
 lem (suc x) =
    der (subst g ∘ f) (suc x)       =< refl >
    mapT suc (subst g (f x))        =< lem1 {f = g} {g = suc} (f x) >
    subst (der g ∘ suc) (f x)       =< cong-app substMap (f x) >
    subst (der g) (mapT suc (f x))  =< refl >
    (subst (der g) ∘ der f) (suc x) □


thm : {X Y Z : Set} -> {g : Y -> Term Z} -> {f : X -> Term Y} -> subst (subst g ∘ f) ≡ (subst g) ∘ (subst f)

thm = funExt lem where
 lem : {X Y Z : Set} -> {g : Y -> Term Z} -> {f : X -> Term Y} -> (t : Term X) ->
          subst (subst g ∘ f) t ≡ (subst g) (subst f t)
 lem {X} {Y} {Z} {g} {f} (var x) = refl
 lem {X} {Y} {Z} {g} {f} (lam t) = cong lam rem
   where rem : subst (der (subst g ∘ f)) t ≡ subst (der g) (subst (der f) t)
         rem = subst (der (subst g ∘ f)) t         =< cong-app (cong subst lemDer) t  >
               subst (subst (der g) ∘ (der f)) t   =< lem t >
               subst (der g) (subst (der f) t)     □
 lem {X} {Y} {Z} {g} {f} (app t0 t1) = cong2 app (lem t0) (lem t1)


lem2 : {X Y Z : Set} -> {g : Y -> Term Z} -> {f : X -> Y} ->
          (t : Term X) -> subst g (mapT f t) ≡ subst (g ∘ f) t

lem2 (var x) = refl
lem2 {X} {Y} {Z} {g} {f} (lam t) = cong lam rem
 where rem :  subst (der g) (mapT (liftM f) t) ≡ subst (der (g ∘ f)) t
       rem =  subst (der g) (mapT (liftM f) t) =< lem2 t >
              subst (der g ∘ liftM f) t        =< cong-app (cong subst (symId lem0)) t >
              subst (der (g ∘ f)) t            □
lem2 (app t0 t1) = cong2 app (lem2 t0) (lem2 t1)

-- unary substitution

unSub : {X : Set} -> Term X -> Maybe X -> Term X
unSub u (suc x) = var x
unSub u zero     = u

-- call by name beta-reduction

data _=>cbn_ {X : Set} : Term X  -> Term X -> Set where
 appl : {t t1 u : Term X} -> t =>cbn t1     -> app t u =>cbn app t1 u
 beta : {t : Term (Maybe X)} -> {u : Term X} -> app (lam t) u =>cbn subst (unSub u) t

-- for instance exY reduces to itself

exRed1 : {X : Set} -> exY {X} =>cbn exY
exRed1 {X} = beta

exRed2 : {X : Set} -> {t : Term X} -> app exId t =>cbn t
exRed2 {X} {t} = beta

exRed3 : {X : Set} -> app (exK {X}) exId =>cbn lam (lam (var zero))
exRed3 {X} = beta


{-

-- general beta-reduction

data bRed : Term -> Term -> Set where
 appl : {t t1 u : Term} -> bRed t t1 -> bRed (app t u) (app t1 u)
 appr : {t u u1 : Term} -> bRed u u1 -> bRed (app t u) (app t u1) 
 lam : {t t1 : Term} -> bRed t t1 -> bRed (lam t) (lam t1)
 beta : {t u : Term} -> bRed (app (lam u) t) (subst [ t ] u)

-}

{-

  The reduction ↦β is non deterministic

  I = lam (var zero)    I   is   λx x

   I I = (λx x) (λx x)   ->   I     Beta

  (I I) (I I) -> (I I) I
        -----          -

or

  (I I) (I I) -> I (I I)
  ----           -

 We don't get the same result!

 Church and Rosser 1936 discovered however that it does not matter

 The reduction is -confluent-

 If   a ->* b   and  a ->* c   then there exists d such that

    b ->* d   and   c  ->* d
 
 Exercise:   define this notion of confluence  in Agda

 This is possible since we have defined ->* in general defined as 

    R is confluent     R* a b   R* a c  -->  there exists d   R* b d and R* c d

 intuitively think of a, b, c  as    processes

 a -> b   means that a becomes b in one step of computation

 Theorem: if a relation -> is confluent and we define  b ~ c by

      there exists d  such that    b ->* d  and  c ->* d

 then the relation ~  is an equivalence relation

 Proof of transitivity:   if we have  a ~ b and b ~ c

      we want a ~ c

 then we have  a ->* d    b ->* d
               b ->* e    c ->* e

 then we have    b ->* d  and b ->* e
 by confluence we have f  such that    d ->* f  and e ->* f

 Since ->* is transitive   and   a ->* d ->* f   we have a ->* f
 Since ->* is transitive   and   c ->* e ->* f   we have c ->* f  
  
 So we have a ~ c    □

  The relation ~ we get   is called   β-conversion    t =_{β} u

 The fact that ↦β   is confluent can be stated precisely since we have
 adopted a de Bruijn representation

 Actually de Bruijn introduced this representation precisely in order to
 prove this confluence property

 N.G. de Bruijn, 1972
 Lambda calculus notation with nameless dummies, a tool for automatic 
    formula manipulation, with application to the Church-Rosser theorem

-}

{-

-- not possible to write an algorithm deciding if a term reduces eventually to a normal form by call-by-name!

-- this is a -deterministic- relation

-- call-by-value, also deterministic relation

data cbvRed : Term -> Term -> Set where
 appl : {t t1 u : Term} -> cbvRed t t1 -> cbvRed (app t (lam u)) (app t1 (lam u))
 appr : {t t1 u : Term} -> cbvRed t t1 -> cbvRed (app u t) (app u t1)
 beta : {t u : Term} -> cbvRed (app (lam u) t) (subst [ t ] u)


delta : Term
delta = lam (app (var zero) (var zero))

omega : Term
omega = app delta delta

redom : cbnRed omega omega
redom = beta



 There is another possible reduction that we can introduce which is 
  η-reduction

 Intuitively it means

    λx  (t x)   ↦η    t    -provided- x is not free in t

 We can add η-reduction on top of β-reduction

 The relation is still confluent


 The corresponding relation ~   is called βη-conversion

   f   ~   λ x (f x)

   t   ~   λ x (t x)

 A consequence of what I said about confluence is the following

 the relation ~     βη-conversion   is -not- trivial

   the variable    x   is not    βη-convertible to   y


-}

-- typed lambda calculus with the substitution theorem

data Typ : Set where
 Base :  Typ
 Arrow : Typ -> Typ -> Typ

context : Set -> Set
context X = X -> Typ

update : {X : Set} -> context X -> Typ -> context (Maybe X)
update {X} G A zero = A
update {X} G A (suc x) = G x

_·_ : {X : Set} -> context X -> Typ -> context (Maybe X)
G · A = update G A

-- hasType G A t   for G |- t : A


data hasType : {X : Set} -> (G : context X) -> (A : Typ) -> (t : Term X) -> Set where
 var : {X : Set} -> {x : X} -> {G : context X} -> hasType G (G x) (var x)
 lam : {X : Set} -> {t : Term (Maybe X)} -> {G : context X} -> {A B : Typ} -> hasType (G · A) B t -> hasType G (Arrow A B) (lam t)
 app : {X : Set} -> {t u : Term X} -> {G : context X} -> {A B : Typ} -> hasType G (Arrow A B) t -> hasType G A u -> hasType G B (app t u)

lemContext1 : {X Y : Set} -> (f : X -> Y) -> (A : Typ) -> (G : context Y) -> (G · A) ∘ (liftM f) ≡ (G ∘ f) · A
lemContext1 {X} {Y} f A G = funExt rem where
 rem : (x : Maybe X) → ((G · A) ∘ liftM f) x ≡ ((G ∘ f) · A) x
 rem zero = refl
 rem (suc x) = refl

substId : {A : Set} -> {a0 a1 : A} -> (P : A -> Set) -> P a1 -> a0 ≡ a1 -> P a0
substId P h refl = h

-- renaming on typing judgement

lemTyp1 :  {X Y : Set} -> {A : Typ} -> {H : context Y} -> {t : Term X} -> (f : X -> Y) -> hasType (H ∘ f) A t -> hasType H A (mapT f t) 

lemTyp1 f var = var
lemTyp1 {H = H} f (lam {t = t} {A = A} {B = B} ht) = lam (lemTyp1 (liftM f) rem1) where
 rem : (H · A) ∘ (liftM f) ≡ (H ∘ f) · A
 rem = lemContext1 f A H
 rem1 : hasType ((H · A) ∘ (liftM f)) B t
 rem1 = substId (λ G -> hasType G B t) ht rem
lemTyp1 f (app ht0 ht1) = app (lemTyp1 f ht0) (lemTyp1 f ht1)

thmSubst : {X Y : Set} -> {A : Typ} -> {G : context X} -> {H : context Y} -> {t : Term X} -> (f : X -> Term Y) ->
              ((x : X) -> hasType H (G x) (f x)) -> hasType G A t -> hasType H A (subst f t)

thmSubst f h (var {x = x}) = h x
thmSubst {X = X} {H = H} f h (lam {t = t} {G = G} {A = A} {B = B} ht) = lam (thmSubst (der f) rem ht) where
 rem : (x : Maybe X) -> hasType (H · A) ((G · A) x) (der f x)
 rem zero = var
 rem (suc x) = lemTyp1 suc (h x)
thmSubst f h (app ht0 ht1) = app (thmSubst f h ht0) (thmSubst f h ht1)


-----------

-- Is this a correct induction principle for Term?


data ⊤ : Set where
 tt : ⊤

liftP : (X : Set) -> (X -> Set) -> (Maybe X) -> Set
liftP X P zero     = ⊤
liftP X P (suc x) = P x

indT :  (F : (X : Set) -> (X -> Set) -> Term X -> Set) -> 
        ((X : Set) -> (P : X -> Set) -> (x : X) -> P x -> F X P (var x)) ->
        ((X : Set) -> (P : X -> Set) -> (t : Term (Maybe X)) -> F (Maybe X) (liftP X P) t -> F X P (lam t)) -> 
        ((X : Set) -> (P : X -> Set) -> (t0 t1 : Term X) -> F X P t0 -> F X P t1 -> F X P (app t0 t1)) ->
        {X : Set} -> (P : X -> Set) -> ((x : X) -> P x) -> (t : Term X) -> F X P t
indT F v l a {X} P h (var x) = v X P x (h x)
indT F v l a {X} P h (lam t) = l X P t (indT F v l a (liftP X P) rem t) where
 rem : (x : Maybe X) -> liftP X P x
 rem zero    = tt
 rem (suc x) = h x
indT F v l a {X} P h (app t0 t1) = a X P t0 t1 (indT F v l a P h t0) (indT F v l a P h t1)


