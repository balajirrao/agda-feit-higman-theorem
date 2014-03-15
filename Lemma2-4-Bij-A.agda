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
open import Function.Equality hiding (_∘_) renaming (cong to Icong)
open import Function.Inverse renaming (sym to Isym; zip to Izip; id to Iid)
open import Function.LeftInverse hiding (_∘_)

open import Function.Bijection hiding (_∘_)

import Data.Fin as F
import Data.Fin.Props as F

open import Function.Related.TypeIsomorphisms

import Relation.Binary.Sigma.Pointwise as SP


open import FinBijections

open import Data.Vec hiding ([_])

open import Misc

open import Lemma2-4-Inv

module Lemma2-4-Bij-A where
  
  ρ-fin : (e f : P) → F.Fin ⌈ suc n /2⌉
  ρ-fin e f = F.fromℕ≤ {ρ e f} (s≤s A₁'-ρ)
    where open Data.Nat.≤-Reasoning
  
  lem-ρ-fin : ∀ {e f} → F.toℕ (ρ-fin e f) ≡ ρ e f
  lem-ρ-fin {e} {f} = F.toℕ-fromℕ≤ (s≤s A₁'-ρ)

  K' : (e f : P) (i : (F.Fin ⌈ suc n /2⌉)) → Set
  K' e f i = Σ (L# e) (λ e₁ → Σ' (P# (el e₁)) (λ e₂ → (e ≢ el e₂) × ρ (el e₂) f ≡ F.toℕ i))

  K : (e f : P) (i : (F.Fin ⌈ suc n /2⌉)) → Set
  K e f i = (Σ' (Neck e) (λ nck → e ≢ neck-e₂ nck × ρ (neck-e₂ nck) f ≡ F.toℕ i))

  K'↔K : (e f : P) (i : (F.Fin ⌈ suc n /2⌉)) → K' e f (F.pred i) ↔ K e f (F.pred i)
  K'↔K e f i = record { to = record { _⟨$⟩_ = λ x → (proj₁ x , el (proj₂ x)) ∶ (pf (proj₂ x)) ; cong = cong _ } ;
                             from = record { _⟨$⟩_ = λ x → (proj₁ (el x)) , ((proj₂ (el x)) ∶ (pf x)) ; cong = cong _ } ;
                             inverse-of = record { left-inverse-of = λ x → refl ; right-inverse-of = λ x → refl } } 

  --≢-helper : ∀ {e e₂ f} →
  --private
  --  helper₀ : ∀ {e} {f} → 

  bij₁ : (e f : P) → {≥1 : True (1 ≤? ρ e f)} {<n : True (suc (ρ e f) ≤? ⌈ n /2⌉)} →
         K e f (F.pred (ρ-fin e f)) ↔ Σ' (Neck e) (λ nck → nck ≡ neck⋆ e f)
  bij₁ e f {≥1} {<n} = record { to = record { _⟨$⟩_ = to ; cong = cong to } ;
                                from = record { _⟨$⟩_ = from ; cong = cong from } ;
                                inverse-of = record { left-inverse-of = λ _ → Σ'≡ refl ; right-inverse-of = λ _ → Σ'≡ refl } }
    where to :  K e f (F.pred (ρ-fin e f)) →  Σ' (Neck e) (λ nck → nck ≡ neck⋆ e f)
          to (nck ∶ ( ≢e , ρ≡) ) = nck ∶ neck! ≢e (0<ρ<n/2⁻¹.class-A nck (trans ρ≡ (trans (≥1-fin-pred (subst (_≤_ 1) (sym lem-ρ-fin) (toWitness ≥1))) (cong pred lem-ρ-fin))) ≢e)
         
   
          from : Σ' (Neck e) (λ nck → nck ≡ neck⋆ e f) →  K e f (F.pred (ρ-fin e f))
          from (nck ∶ ≡⋆) = nck ∶ ({!!} , ρe₂f≡)
            where .ρe₂f≡ : _
                  ρe₂f≡ = (trans (0<ρ<n/2.class-A-ρ {≥1 = ≥1} {<n = <n} nck (cong neck-e₂ ≡⋆)) (sym (trans (≥1-fin-pred (subst (_≤_ 1) (sym lem-ρ-fin) (toWitness ≥1))) (cong pred lem-ρ-fin))))

  bij₂ : (e f : P) → {≥1 : True (1 ≤? ρ e f)} {<n : True (suc (ρ e f) ≤? ⌈ (pred n) /2⌉)} →
         K e f (ρ-fin e f) ↔ Σ' (Neck e) (λ nck → ((neck-e₁ nck) ≡ (neck-e₁ (neck⋆ e f)) × (neck-e₂ nck) ≢ (neck-e₂ (neck⋆ e f))) × e ≢ (neck-e₂ nck))
  bij₂ e f = record { to = record { _⟨$⟩_ = to ; cong = cong to } ;
                                from = record { _⟨$⟩_ = from ; cong = cong from } ;
                                inverse-of = record { left-inverse-of = λ _ → Σ'≡ refl ; right-inverse-of = λ _ → Σ'≡ refl } }
    where to : K e f (ρ-fin e f) → Σ' (Neck e) (λ nck → ((neck-e₁ nck) ≡ (neck-e₁ (neck⋆ e f)) × (neck-e₂ nck) ≢ (neck-e₂ (neck⋆ e f))) × e ≢ (neck-e₂ nck))
          to (nck ∶ (≢e , ρ≡)) = nck ∶ (0<ρ<predn/2⁻¹.class-B nck (trans ρ≡ lem-ρ-fin) ≢e , ≢e)
  
          from : Σ' (Neck e) (λ nck → ((neck-e₁ nck) ≡ (neck-e₁ (neck⋆ e f)) × (neck-e₂ nck) ≢ (neck-e₂ (neck⋆ e f))) × e ≢ (neck-e₂ nck)) → K e f (ρ-fin e f)
          from (nck ∶ ((≡e₁⋆ , ≢e₂⋆) , ≢e)) = nck ∶ (≢e , (trans (0<ρ<n/2.class-B-ρ {<n = {!!}}  nck ≡e₁⋆ ≢e₂⋆ (≢sym ≢e)) (sym lem-ρ-fin)))

  
