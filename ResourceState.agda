open import Data.Nat
open import Data.Vec
open import Env
module ResourceState (n n' nI : ℕ) (ts : Vec Simple-Ty n) (ts' : Vec Simple-Ty n') (tI : Vec Simple-Ty nI) where
open import IO
open import Data.Unit
open import Data.Fin
open import Data.Product

data Ty : Set₁ where
  Ty-Unit : Ty
  Ty-Lift : Set → Ty
  Ty-S : Simple-Ty → Ty

El-Ty : Ty → Set
El-Ty Ty-Unit = ⊤
El-Ty (Ty-Lift A) = A
El-Ty (Ty-S s) = El-Simple s

data Lang : {n n' : ℕ} → Vec Simple-Ty n → Vec Simple-Ty n' → Ty → Set₁ where
  ACTION : IO ⊤ → Lang {n} {n} ts ts Ty-Unit
  RETURN : {A : Set} → A → Lang {n} {n} ts ts (Ty-Lift A)
  BIND   : {ty tyout : Ty} →
           Lang ts tI ty →
           (El-Ty ty → Lang tI ts' tyout) →
           Lang ts ts' tyout

  GET : (i : Fin n) → Lang {n} {n} ts ts (Ty-S (lookup i ts))
  SET : ∀ {T} (i : Fin n) → El-Simple T → ElemIs i T ts → Lang {n} {n} ts ts Ty-Unit

interp : ∀ {T} → S-Env ts → Lang ts ts' T → IO (S-Env ts' × El-Ty T)
interp _ _ = {!!}
