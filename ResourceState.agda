open import Data.Nat
open import Data.Vec hiding (_>>=_)
open import Env
module ResourceState where
open import IO
open import Coinduction
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
  ACTION : {n : ℕ} {ts : Vec Simple-Ty n} → IO ⊤ → Lang ts ts Ty-Unit
  RETURN : {n : ℕ} {ts : Vec Simple-Ty n} {A : Set} → A → Lang ts ts (Ty-Lift A)
  BIND   : {ty tyout : Ty} {n n' nI : ℕ}
           {ts : Vec Simple-Ty n} {ts' : Vec Simple-Ty n'} {tI : Vec Simple-Ty nI} →
           Lang ts tI ty →
           (El-Ty ty → Lang tI ts' tyout) →
           Lang ts ts' tyout

  GET : {n : ℕ} {ts : Vec Simple-Ty n}
        (i : Fin n) → Lang ts ts (Ty-S (lookup i ts))
  SET : ∀ {T n} {ts : Vec Simple-Ty n} 
        (i : Fin n) → El-Simple T → ElemIs i T ts → Lang {n} {n} ts ts Ty-Unit

interp : ∀ {T n n'} {ts : Vec Simple-Ty n} {ts' : Vec Simple-Ty n'} →
         S-Env ts → Lang ts ts' T → IO (S-Env ts' × El-Ty T)
interp env (ACTION io) =
  ♯₁ io >>
  ♯₁ return (env , tt)
interp env (RETURN x) = return (env , x)
interp env (BIND y y') = {!!}
interp env (GET i) = {!!}
interp env (SET i y y') = {!!}
