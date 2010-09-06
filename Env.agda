module Env where
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Fin
open import Data.Vec

infixr 5 _∷_

data Env {R : Set} (El-R : R → Set) : ∀ {n} (xs : Vec R n) → Set where
  [] : Env El-R []
  _∷_ : ∀ {x n} {xs : Vec R n} (res : El-R x) → Env El-R xs → Env El-R (x ∷ xs)

data Simple-Ty : Set where
  S-Nat S-Bool S-Unit : Simple-Ty

El-Simple : Simple-Ty → Set
El-Simple S-Nat  = ℕ
El-Simple S-Bool = Bool
El-Simple S-Unit = ⊤

S-Env : ∀ {n} (xs : Vec Simple-Ty n) → Set
S-Env = Env El-Simple

s-Ty : Vec Simple-Ty 2
s-Ty = S-Nat ∷ S-Bool ∷ []

s-Env : S-Env s-Ty
s-Env = 2 ∷ true ∷ []

add-end : {n : ℕ} {R : Set} {El-R : R → Set} {end : R} {xs : Vec R n} →
  Env El-R xs → El-R end → Env El-R (xs ∷ʳ end)
add-end [] y = y ∷ []
add-end (x ∷ xs) y = x ∷ add-end xs y

drop-end : {n : ℕ} {R : Set} {El-R : R → Set} {end : R} {xs : Vec R n} →
  Env El-R (xs ∷ʳ end) → Env El-R xs
drop-end {xs = []} xs = []
drop-end {xs = v ∷ vs} (x ∷ xs) = x ∷ drop-end xs

lookup-Env : ∀ {n R El-R} {xs : Vec R n}
  (i : Fin n) → Env {R} El-R xs → El-R (lookup i xs)
lookup-Env zero (x ∷ _) = x
lookup-Env (suc i) (_ ∷ xs) = lookup-Env i xs

homo-update-Env : {n : ℕ} {R : Set} {El-R : R → Set} {xs : Vec R n} →
  Env El-R xs → (i : Fin n) → El-R (lookup i xs) → Env El-R xs
homo-update-Env [] () y
homo-update-Env (_ ∷ xs) zero y = y ∷ xs
homo-update-Env (x ∷ xs) (suc i) y = x ∷ homo-update-Env xs i y

update-Env : {n : ℕ} {R : Set} {El-R : R → Set} {new : R} {xs : Vec R n} →
  Env El-R xs → (i : Fin n) → El-R new → Env El-R (xs [ i ]≔ new)
update-Env [] () y
update-Env (_ ∷ xs) zero y = y ∷ xs
update-Env (x ∷ xs) (suc i) y = x ∷ update-Env xs i y
