module Lecture1 where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

not : Bool → Bool
not false = true
not true = false

_&&_ : Bool → Bool → Bool
false && y = false
true && y = y

-- if_then_else : Bool → Nat → Nat → Nat
-- if false then x else _ = y
-- if true then _ else y = x

-- {} denote an implicit argument
if_then_else : {A : Set} → Bool → A → A → A 
if false then x else y = y
if true then x else y = x


mutual 

    data Cond : Set where
        neg : Cond → Cond
        lt : Expr → Expr → Cond

    data Expr : Set where
        lit : Nat → Expr
        add : Expr → Expr → Expr
        if : Cond → Expr → Expr → Expr

evalCond : Cond → Bool
eval : Expr → Nat

eval (lit n) = n
eval (add e1 e2) = eval e1 + eval e2
eval (if b x y) = if (evalCond b) then (eval x) else (eval y)

evalCond (neg c) = not (evalCond c)
evalCond (lt a b) = (eval a) < (eval b)
