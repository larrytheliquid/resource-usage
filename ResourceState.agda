open import Data.Nat
open import Data.Vec
module ResourceState (R : Set) (n n' nI : ℕ) (ts : Vec R n) (ts' : Vec R n') (tI : Vec R nI) where
open import IO
open import Data.Unit
open import Env

data Ty : Set₁ where
  Ty-Unit : Ty
  Ty-Lift : Set → Ty

El-Ty : Ty → Set
El-Ty Ty-Unit = ⊤
El-Ty (Ty-Lift A) = A

data Lang : {n n' : ℕ} → Vec R n → Vec R n' → Ty → Set₁ where
  ACTION : IO ⊤ → Lang {n} {n} ts ts Ty-Unit
  RETURN : {A : Set} → A → Lang ts ts' (Ty-Lift A)
  BIND   : {ty tyout : Ty} →
           Lang ts tI ty →
           (El-Ty ty → Lang tI ts' tyout) →
           Lang ts ts' tyout
