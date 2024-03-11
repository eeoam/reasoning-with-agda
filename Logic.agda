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

cong₂ : 
    {A B C : Set} (f : A → B → C) {u x : A} {v y : B} →
    u ≈ x → v ≈ y → f u v ≈ f x y
cong₂ f refl refl = refl 

cong-app : {A B : Set} {f g : A → B} → f ≈ g → (x : A) → f x ≈ g x
cong-app refl x = refl

subst : {A : Set} {x y : A} (P : A → Set) → x ≈ y → P x → P y
subst P refl Px = Px

module ≈-Reasoning {A : Set} where

    infix 1 begin_


-- Load       C-c C-l
-- Case split C-c C-c
-- Fill hole  C-c C-space
-- Refine C-c C-r
-- Agda guess C-c C-a