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
    infixr 2 _≈⟨⟩_ _≈⟨_⟩_
    infix 3 _∎

    begin_ : {x y : A} → x ≈ y → x ≈ y
    begin p = p

    _≈⟨⟩_ : (x : A) {y : A} → x ≈ y → x ≈ y
    x ≈⟨⟩ p = p

    _≈⟨_⟩_ : (x : A) {y z : A} → x ≈ y → y ≈ z → x ≈ z
    _≈⟨_⟩_ x p q = trans p q

    _∎ : (x : A) → x ≈ x
    x ∎ = refl

open ≈-Reasoning

trans' : {A : Set} {x y z : A} → x ≈ y → y ≈ z → x ≈ z
trans' {A} {x} {y} {z} x≈y y≈z =
    begin
    x
    ≈⟨ x≈y ⟩
    y
    ≈⟨ y≈z ⟩
    z ∎

data Bool : Set where
    true : Bool
    false : Bool

infix 5 _≡_
_≡_ : Bool → Bool → Bool
true ≡ b = b
false ≡ true = false
false ≡ false = true 

≡-sym : {a b : Bool} → (a ≡ b) ≡ (b ≡ a) ≈ true
≡-sym {true} {true} = refl
≡-sym {true} {false} = refl
≡-sym {false} {true} = refl
≡-sym {false} {false} = refl

≡-assoc : {a b c : Bool} → (a ≡ (b ≡ c)) ≡ ((a ≡ b) ≡ c) ≈ true
≡-assoc {true} {true} {true} = refl
≡-assoc {true} {true} {false} = refl
≡-assoc {true} {false} {true} = refl
≡-assoc {true} {false} {false} = refl
≡-assoc {false} {true} {true} = refl
≡-assoc {false} {true} {false} = refl
≡-assoc {false} {false} {true} = refl
≡-assoc {false} {false} {false} = refl

infix 6 _∨_
_∨_ : Bool → Bool → Bool
true ∨ b = true
false ∨ b = b

∨-idem : {a : Bool} → a ∨ a ≡ a ≈ true
∨-idem {true} = refl
∨-idem {false} = refl

∨-unitr : {a : Bool} → a ∨ false ≈ a
∨-unitr {true} = refl
∨-unitr {false} = refl

∨-sym : {a b : Bool} → a ∨ b ≡ b ∨ a ≈ true
∨-sym {true} {true} = refl
∨-sym {true} {false} = refl
∨-sym {false} {true} = refl
∨-sym {false} {false} = refl

∨-assoc : {a b c : Bool} → a ∨ (b ∨ c) ≡ (a ∨ b) ∨ c ≈ true
∨-assoc {true} {true} {true} = refl
∨-assoc {true} {true} {false} = refl
∨-assoc {true} {false} {true} = refl
∨-assoc {true} {false} {false} = refl
∨-assoc {false} {true} {true} = refl
∨-assoc {false} {true} {false} = refl
∨-assoc {false} {false} {true} = refl
∨-assoc {false} {false} {false} = refl

∨-over-≡ : {a b c : Bool} → a ∨ (b ≡ c) ≡ (a ∨ b ≡ a ∨ c) ≈ true
∨-over-≡ {true} {true} {true} = refl
∨-over-≡ {true} {true} {false} = refl
∨-over-≡ {true} {false} {true} = refl
∨-over-≡ {true} {false} {false} = refl
∨-over-≡ {false} {true} {true} = refl
∨-over-≡ {false} {true} {false} = refl
∨-over-≡ {false} {false} {true} = refl
∨-over-≡ {false} {false} {false} = refl

-- Load       C-c C-l
-- Case split C-c C-c
-- Fill hole  C-c C-space
-- Refine C-c C-r    
-- Agda guess C-c C-a