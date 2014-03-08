open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import Relation.Binary.PropositionalEquality as PropEq hiding (proof-irrelevance)

open import Data.Empty
open import Data.Unit hiding (_≤?_; _≤_; _≟_)

open import Data.Product 

open import Data.Bool hiding (_≟_)

open import Data.Nat hiding (compare) renaming (_≟_ to _ℕ≟_)
--open Data.Nat.≤-Reasoning

--open import Function.Inverse
open import Data.Sum

open import Data.Nat.Properties
open SemiringSolver

open import Function hiding (_∘_)
open import Function.Equality hiding (cong;  _∘_)
open import Function.Inverse hiding (sym)
open import Function.LeftInverse hiding (_∘_)

import Data.Fin as Fin
import Data.Fin.Properties as Fin

open import FinBijections

open import Misc

module Lemma2-4-A where
  
  open import Lemma2-4
            
--   -- M : P → P → ℕ → Set
--   -- M e f q = Subset (ppchain e f) (λ x → ρ' x ≡ q)

--   -- -- Use equivalence here maybe
--   -- lem₀ : ∀ {e} → ρ e e ≡ 0
--   -- lem₀ {e} = helper (sppc-ρ-shorter-than [ e ])
--   --   where helper : ∀ {x} → x ≤ 0 → x ≡ 0
--   --         helper z≤n = refl

--   -- lem₁ : ∀ {e f} → ρ e f ≡ 0 → e ≡ f
--   -- lem₁ {e} {f} eq with sppc e f
--   -- lem₁ eq | [ e ] = refl
--   -- lem₁ () | _∶⟨_⟩∶_ e e₁ c {{e#e₁}} {{e₁#e₂}}

--   -- F : (e f e' f' : P) (q : ℕ) → ρ e f ≡ ρ e' f' → M e f q → M e' f' q
--   -- F e .e e' f' zero ρ≡ ([ .e ] , ρ'≡0) rewrite lem₀ {e} | lem₁ (sym ρ≡) = [ f' ] , refl
--   -- F e f e' f' zero ρ≡ (_∶⟨_⟩∶_ .e e₁ c {{e#e₁}} {{e₁#e₂}} , ())
--   -- F e .e e' f' (suc q) ρ≡ ([ .e ] , ())
--   -- F e f e' f' (suc q) ρ≡ (_∶⟨_⟩∶_ {e₂} .e e₁ c {{e#e₁}} {{e₁#e₂}} , p) = {!e' ∶⟨ e₁' ⟩∶ ppc!} , {!!}
--   --   where
--   --         e₁' = {!!}
--   --         e₂' : P
--   --         e₂' = {!!}
--   --         ppc = {!F e₂ f  e₂' f' q ? _!}
