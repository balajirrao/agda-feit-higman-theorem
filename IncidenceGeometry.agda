open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq

open import Data.Empty

open import Data.Nat hiding (_≟_)

import Level

module IncidenceGeometry where

  postulate
    P L : Set

  data O : Set where
    pt : P → O
    ln : L → O

  postulate
    _#_ : Rel O Level.zero
    _#?_ : Decidable _#_
    _≟_ : Decidable {A = O} _≡_
    
    #sym : ∀ {e f} → e # f → f # e
    #refl : ∀ {e} → e # e

  infixr 5 _∷_   
  data chain : O → O → Set where
    [_] : (e : O) → chain e e
    _∷_ : ∀ {f g} (e : O) {{e<>f : False (e ≟ f)}} {{e#f : True (e #? f)}} (c : chain f g) → chain e g    

  len : ∀ {e f} (c : chain e f) → ℕ
  len [ _ ] = zero
  len (_ ∷ c) = suc (len c)

  head : ∀ {e f} (c : chain e f) → O
  head {e} _ = e

  second :  ∀ {e f} (c : chain e f) → {{≥1 : True (1 ≤? len c)}} → O
  second {.f} {f} [ .f ] {{()}}
  second (_ ∷ c) {{_}} = head c

  tail : ∀ {e f} (c : chain e f) → {{≥1 : True (1 ≤? len c)}} → chain (second c) f
  tail {.f} {f} [ .f ] {{()}}
  tail {e} (.e ∷ c) {{_}} = c

