module Logic where

-- Equality

infix 4 _≈_
data _≈_ {A : Set} (x : A) : A -> Set where
    refl : x ≈ x

-- A variant of `refl` where the argument is explicit.
pattern erefl x = refl {x = x}

-- ≈ is an equivalence relation
sym : {A : Set} {x y : A} → x ≈ y → y ≈ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≈ y → y ≈ z → x ≈ z
trans refl q = q

-- Congruence
cong : {A B : Set} (f : A → B) → {x y : A} → x ≈ y → f x ≈ f y
cong f refl = refl

-- Load       C-c C-l
-- Case split C-c C-c
-- Fill hole  C-c C-space
-- Refine C-c C-r
-- Agda guess C-c C-a