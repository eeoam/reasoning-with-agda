module Logic where

-- Equality

infix 4 _≈_
data _≈_ {A : Set} (x : A) : A -> Set where
    refl : x ≈ x

-- A variant of `refl` where the argument is explicit.
pattern erefl x = refl {x = x}

-- Load       C-c C-l
-- Case split C-c C-c
-- Fill hole  C-c C-space
-- Refine C-c C-r
-- Agda guess C-c C-a