{-#  OPTIONS --type-in-type #-}

module Nontermination where

data ⊥ : Set where

not : Set -> Set
not A = A -> ⊥

{-# NO_POSITIVITY_CHECK #-}
data Liar : Set where
 tellLies : not Liar -> Liar


nLiar : not Liar
nLiar (tellLies x) = x (tellLies x)

liar : Liar
liar = tellLies nLiar

nonTerminating : ⊥
nonTerminating = nLiar liar


{-# NO_POSITIVITY_CHECK #-}
data Bad : Set where
 lam : (Bad -> Bad) -> Bad

app : Bad -> Bad -> Bad
app (lam f) y = f y

delta : Bad
delta = lam (λ x -> app x x)

loop : Bad
loop = app delta delta

variable
 A : Set

{-# NON_TERMINATING #-}
bad : A
bad = bad


-- tree of all trees

data tree : Set where
 root : {A : Set} -> (A -> tree) -> tree

data Id {A : Set} : A -> A -> Set where
  refl : (x : A) -> Id x x


isBad : tree -> Set
isBad (root {A} f) = (x : A) -> not (Id (f x) (root f))

data bTrees : Set where
 pair : (x : tree) -> isBad x -> bTrees

pi1 : bTrees -> tree
pi1 (pair x _) = x

t0 : tree
t0 = root pi1

lem0 : (t t' : tree) -> isBad t -> Id t t' -> isBad t'
lem0 t .t h (refl .t) = h

bt0 : isBad t0
bt0 (pair t bt) h = rem1 (pair t bt) h
 where
  rem1 : isBad t0
  rem1 = lem0 t t0 bt h
 
loop0 : ⊥
loop0 = bt0 (pair t0 bt0) (refl t0)
