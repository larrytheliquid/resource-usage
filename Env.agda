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

private
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

postulate
  lookup-Env : ∀ {n R El-R} {xs : Vec R n}
    (i : Fin n) → Env {R} El-R xs → El-R (lookup i xs)
  update-Env : {n : ℕ} {R : Set} {El-R : R → Set} {new : R} {xs : Vec R n} →
    Env El-R xs → (i : Fin n) → El-R new → Env El-R (xs [ i ]≔ new)
  add-end : {n : ℕ} {R : Set} {El-R : R → Set} {end : R} {xs : Vec R n} →
    Env El-R xs → El-R end → Env El-R (xs ∷ʳ end)
  drop-end : {n : ℕ} {R : Set} {El-R : R → Set} {end : R} {xs : Vec R n} →
    Env El-R (xs ∷ʳ end) → Env El-R xs
