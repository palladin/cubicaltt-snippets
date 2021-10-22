{-# OPTIONS --cubical #-}
 
open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Data.List
open import Data.Nat
open import Data.Bool
open import Data.String
 
variable
  ℓ : Level
 
_×_ : Type ℓ → Type ℓ → Type ℓ
_×_ A B = Σ A (λ _ → B)

DB : Type₀
DB = List (ℕ × (String × ((ℕ × ℕ) × ℕ)))

There : Type₀ → Type₀
There A = List (ℕ × (String × (A × ℕ)))

swapf : {A B : Type ℓ} → A × B → B × A
swapf (x , y) = (y , x)
 
swap : {A B : Type ℓ} (x : A × B) → swapf (swapf x) ≡ x
swap x i = x
 
swapEq : (ℕ × ℕ) ≃ (ℕ × ℕ)
swapEq = isoToEquiv (iso swapf swapf swap swap) 

swapPath : (ℕ × ℕ) ≡ (ℕ × ℕ)
swapPath = ua swapEq

convert : DB → DB
convert db = subst There swapPath db

euro : DB
euro = (4 , "John" , (30 , 5) , 1956) ∷
       (8 , "Hugo" , (29 , 12) , 1978) ∷
       (15 , "James" , (1 , 7) , 1968) ∷
       (16 , "Sayid" , (2 , 10) , 1967) ∷
       (23 , "Jack" , (3 , 12) , 1969) ∷
       (42 , "Sun" , (20 , 3) , 1969) ∷
       []

american : DB
american = (4 , "John" , (5 , 30) , 1956) ∷
           (8 , "Hugo" , (12 , 29) , 1978) ∷
           (15 , "James" , (7 , 1) , 1968) ∷
           (16 , "Sayid" , (10 , 2) , 1967) ∷
           (23 , "Jack" , (12 , 3) , 1969) ∷
           (42 , "Sun" , (3 , 20) , 1969) ∷
           []

test : convert euro ≡ american
test i = american
