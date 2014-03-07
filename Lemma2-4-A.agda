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
open import Function.Inverse
open import Function.LeftInverse hiding (_∘_)

import Data.Fin as Fin
import Data.Fin.Properties as Fin

open import FinBijections

open import Misc

module Lemma2-4-A where
  
  open import Lemma2-4
  open import Lemma2-1
 
  module ρ≡n/2 {e f : P} {n-even : Even (n)} {≡n/2 : True ( ⌈ (n) /2⌉ ℕ≟ ρ e f)} where

    private
      λ≡n : lambda (pt e) (pt f) ≡ n
      λ≡n = PropEq.sym (
            begin
              n
                ≡⟨ PropEq.sym (lem-2x⌈n/2⌉-even n-even) ⟩
              2 * ⌈ n /2⌉ 
                ≡⟨ cong (_*_ 2) (toWitness ≡n/2) ⟩
              2 * ρ e f
                ≡⟨ PropEq.sym lem-2xρ-lambda ⟩
              (lambda (pt e) (pt f) ∎))
        where open ≡-Reasoning

      chain-with-neck : (nck : Neck e) → chain (pt e) (pt f)
      chain-with-neck nck = proj₁ $ Inverse.from (I e (pt f) λ≡n) ⟨$⟩ l#e
        where l#e : L# e
              l#e = (neck-e₁ nck) , neck-e#e₁ nck

      ppc-with-neck : (nck : Neck e) → ppchain e f
      ppc-with-neck nck = chain-with-neck nck as-ppc

      ρ'ppc≡n : (nck : Neck e) → ρ' (ppc-with-neck nck) ≡ ⌈ (n) /2⌉
      ρ'ppc≡n nck rewrite PropEq.sym (lem-lambda/2-ρ {e} {f}) |
                          PropEq.sym (lem-len/2-ρ {ppc = ppc-with-neck nck}) |
                          lem-id₀ {c = sc (pt e) (pt f)} |
                          lem-id₀ {c = chain-with-neck nck} =
                            trans (cong ⌊_/2⌋ lenc≡n) (lem-even⇒⌊≡⌋ n-even)
        where l#e : L# e
              l#e = (neck-e₁ nck) , neck-e#e₁ nck
              lenc≡n = proj₂ $ Inverse.from (I e (pt f) λ≡n) ⟨$⟩ l#e
      
      ρ'ppc≥1 : (nck : Neck e) → ρ' (ppc-with-neck nck) ≥ 1
      ρ'ppc≥1 nck = begin 1 ≤⟨ s≤s z≤n ⟩ ⌈ (n) /2⌉ ≡⟨ PropEq.sym (ρ'ppc≡n nck) ⟩ (ρ' (ppc-with-neck nck) ∎)
        where open Data.Nat.≤-Reasoning

      ppc-shortest : (nck : Neck e) → (ppc-with-neck nck) is-ρ-shortest
      ppc-shortest nck = trans (ρ'ppc≡n nck) (toWitness ≡n/2)

      e₂⋆ : (nck : Neck e) → P
      e₂⋆ nck = (neck-e₂ $ ppneck (ppc-with-neck nck) {fromWitness (ρ'ppc≥1 nck)})
    
    class-A₀-ρ : (nck : Neck e) → (neck-e₂ nck) ≡ (e₂⋆ nck) → ρ (neck-e₂ nck) f ≡ pred ⌈ (n) /2⌉
    class-A₀-ρ nck eq = begin
                       ρ e₂ f
                         ≡⟨ cong ((Function.flip ρ) f) eq ⟩
                       ρ (e₂⋆ nck) f
                         ≡⟨ PropEq.sym (tailpp-ρ-shortest (ppc-shortest nck)) ⟩
                       ρ' (tailpp (ppc-with-neck nck))
                         ≡⟨ lem-tailpp-ρ {ppc = ppc-with-neck nck} ⟩
                       pred (ρ' (ppc-with-neck nck))
                         ≡⟨ cong pred (ρ'ppc≡n nck) ⟩
                       (pred ⌈ n /2⌉ ∎)                                                                                
      where open ≡-Reasoning
            e₂ = neck-e₂ nck

    class-A₁-ρ :  (nck : Neck e) → (neck-e₂ nck) ≢ (e₂⋆ nck) → ρ (neck-e₂ nck) f ≡ ⌈ (n) /2⌉
    class-A₁-ρ nck neq = {!!}
      
                  
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
