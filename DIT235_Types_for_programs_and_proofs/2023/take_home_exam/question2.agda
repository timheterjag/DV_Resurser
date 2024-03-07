
module question2 where

open import ExamPrelude

-- Note that some holes may not be solvable!
-- In these cases comment out the definition and explain informally
-- why you don't expect the statement to be provable.

-- (a)

q2a : (A ∨ B) ∧ (A ∨ C) → A ∨ (B ∧ C)
q2a = {!!}

-- (b)

q2b : ((A ∧ B) → C) → (A → C) ∨ (B → C)
q2b = {!!}

-- (c)

q2c : (A ∨ B → C) → (A → C) ∧ (B → C)
q2c = {!!}

-- (d)

q2d : {B : A → Set} → ¬ (Σ A B) → (x : A) → ¬ (B x)
q2d = {!!}

-- (e)

q2e : {B : A → Set} → ¬ ((x : A) → ¬ (B x)) → Σ A B
q2e = {!!}
