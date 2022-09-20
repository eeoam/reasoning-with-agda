module Naturals where

data ℕ : Set where
    zero : ℕ
    succ : ℕ -> ℕ

{-
[| Nat |] = ℕ
[| zero |] = 0
[| succ n |] = 1 + [| n |]
-}


{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

{-
[| _+_ |] = _+_

[| zero + n |] 
= [| zero |] + [| n |]
= 0 + [| n |]
= [| n |]

[| (succ n) + m|] 
= [| (succ n) |]  + [| m |]
= (1 + [| n |]) + [| m |]
=  1 + ([| n |] + [| m |])
=  1 + ([| n + m |])
=  [| succ (n + m ) |]
-}

_+_ : ℕ -> ℕ -> ℕ
zero + m = m
(succ n) + m = succ (n + m)

{-
[| m * n |] = [| m |] * [| n |]   

[| zero * n|] 
= [| zero |] * [| n |]  
= 0 * [| n |]
= 0

[| succ m * n|]
= [| succ m |] * [| n |]
= (1 + [| m |] ) * [| n |]
= 1 * [| n |] + [| m |] * [| n |]
= [| n |] + [| m |] * [| n |]          
-}

_*_ : ℕ -> ℕ -> ℕ
zero * n = zero
(succ m) * n = n + (m * n)

{-
[| m ^ n |] = [| m |] ^ [| n |]   

[| m ^ zero |] 
= [| m |] ^ [| zero |]  
= [| m |] ^ 0
= 1
= [| succ zero |]

[| m ^ succ n|]
= [| m |] ^ [| succ n |]
= [| m |]  ^ (1 + [| n |])
= [| m |] * [| m |] ^ [| n |]
= [| m |] * [| m  ^ n |]           
-}

_^_ : ℕ -> ℕ -> ℕ
m ^ zero = succ zero
m ^ succ n = m * (m ^ n)

{-
[| m ∸ n |] = [| m |] ∸ [| n |]   

[| m ∸ zero |] 
= [| m |] ∸ [| zero |]  
= [| m |] ∸ 0
= [| m |]

[| zero ∸ succ n|]
= [| zero |] ∸ [| succ n |]
= 0  ∸ [| succ n |]
=  0  ∸ (1 + [| n |])
= 0
= [| zero |]  

[| succ m ∸ succ n|]
= [| succ m |] ∸ [| succ n|]
= (1 + [| m |]) ∸ (1 + [| n |])
= (1 ∸ 1 + [| m |] ∸ [| n |])
= [| m |] ∸ [| n |]
= [| m  ∸  n |]
-}

_∸_ : ℕ -> ℕ -> ℕ
m ∸ zero = m
zero ∸ succ n = zero
succ m ∸ succ n = m ∸ n

infixl 6 _+_ _∸_
infixl 7 _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- Load       C-c C-l
-- Case split C-c C-c
-- Fill hole  C-c C-space
-- Refine C-c C-r
-- Agda guess C-c C-a