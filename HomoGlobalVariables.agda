open import Data.Nat
open import Data.Vec hiding (_>>=_)
open import Env
module HomoGlobalVariables where
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
  SET : ∀ {n} {ts : Vec Simple-Ty n} 
        (i : Fin n) → El-Simple (lookup i ts) → ElemIs i (lookup i ts) ts → Lang ts ts Ty-Unit

mutual
  interp-BIND : ∀ {A B n n'} {ts : Vec Simple-Ty n} {ts' : Vec Simple-Ty n'} →
                S-Env ts × A → (A → Lang ts ts' B) →
                IO (S-Env ts' × El-Ty B)
  interp-BIND (env , val) f = interp env (f val)

  interp : ∀ {T n n'} {ts : Vec Simple-Ty n} {ts' : Vec Simple-Ty n'} →
           S-Env ts → Lang ts ts' T → IO (S-Env ts' × El-Ty T)
  interp env (ACTION io) =
    ♯₁ io >>
    ♯₁ return (env , tt)
  interp env (RETURN val) = return (env , val)
  interp env (BIND prog f) =
    ♯₁ interp env prog >>= λ ans →
    ♯₁ interp-BIND ans f
  interp env (GET i) =
    return (env , lookup-Env i env)
  interp env (SET i val _) =
    return (homo-update-Env env i val , tt)
