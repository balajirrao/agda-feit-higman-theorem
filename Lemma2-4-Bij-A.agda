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

open import Function.Equivalence hiding (sym)

open import FinBijections

open import Data.Vec hiding ([_])

open import Misc

open import Lemma2-4-Inv

module Lemma2-4-Bij-A where
  postulate
    Σ↔ : 
        {A₁ A₂ : Set}
        {B₁ : A₁ → Set} {B₂ : A₂ → Set}
        (A₁↔A₂ : A₁ ↔ A₂) →
        (∀ {x} → B₁ x ⇔ B₂ (Inverse.to A₁↔A₂ ⟨$⟩ x)) →
        (Σ A₁ B₁) ↔ Σ A₂ B₂ 

  ρ-fin : (e f : P) → F.Fin ⌈ suc n /2⌉
  ρ-fin e f = F.fromℕ≤ {ρ e f} (s≤s A₁'-ρ)
    where open Data.Nat.≤-Reasoning
  
  lem-ρ-fin : ∀ {e f} → F.toℕ (ρ-fin e f) ≡ ρ e f
  lem-ρ-fin {e} {f} = F.toℕ-fromℕ≤ (s≤s A₁'-ρ)
{-
  K' : (e f : P) (i : (F.Fin ⌈ suc n /2⌉)) → Set
  K' e f i = Σ (L# e) (λ e₁ → Σ' (P# (el e₁))
             (λ e₂ → (e ≢ el e₂) × ρ (el e₂) f ≡ F.toℕ i))
-}
{-
  K'↔K : (e f : P) (i : (F.Fin ⌈ suc n /2⌉)) →
                K' e f (F.pred i) ↔ K e f (F.pred i)
  K'↔K e f i = record {
               to =
                 record {
                   _⟨$⟩_ = λ x → (proj₁ x , el (proj₂ x)) ∶ (pf (proj₂ x))
                   ; cong = cong _ }
               ; from =
                 record {
                   _⟨$⟩_ = λ x → (proj₁ (el x)) , ((proj₂ (el x)) ∶ (pf x))
                 ; cong = cong _ }
               ; inverse-of =
                 record {
                   left-inverse-of = λ _ → refl
               ; right-inverse-of = λ _ → refl
             } } -}

  ρ≥1 : ∀ {e f r} → (ρ≡r : ρ e f ≡ r) → {≥1 : True (1 ≤? r)} → True (1 ≤? ρ e f)
  ρ≥1 refl {x} = x

  bij₁ : ∀ {e f r} → (ρ≡r : ρ e f ≡ r) → {≥1 : True (1 ≤? r)}
                     {<n : True (suc r ≤? ⌈ n /2⌉)} →
         K e f (pred r) ↔ Σ (Neck e) (λ nck → nck ≡ neck⋆ e f {ρ≥1 ρ≡r})

  bij₁ {e} {f} {._} refl {≥1} {<n} = Σ↔ Iid (λ {x} → record { to = record { _⟨$⟩_ = to ; cong = cong (to {x}) } ; from = record { _⟨$⟩_ = from ; cong = cong from } })
    where
      to : {nck : Neck e} → (neck-e₂ nck ≢ e × ρ (neck-e₂ nck) f ≡ pred (ρ e f)) → nck ≡ neck⋆ e f
      to {nck} ( ≢e , ρ≡)  = neck! (≢sym ≢e)
                             (0<ρ<n/2⁻¹.class-A nck
                               ρ≡ (≢sym ≢e))
         
      from : {nck : Neck e} → nck ≡ neck⋆ e f → neck-e₂ nck ≢ e × ρ (neck-e₂ nck) f ≡ pred (ρ e f)
      from {nck} ≡⋆ = ((λ eq → lem-neck⋆ (sym $ subst (λ z → e ≡ neck-e₂ z) ≡⋆ (sym eq))) , 0<ρ<n/2.class-A-ρ {≥1 = ≥1} {<n = <n} nck (cong neck-e₂ ≡⋆))


  bij₂ : ∀ {e f r} → (ρ≡r : ρ e f ≡ r) → {≥1 : True (1 ≤? r)} {<predn : True (suc r ≤? ⌈ (pred n) /2⌉)} →
         K e f r ↔ Σ (Neck e) (λ nck → ((neck-e₁ nck) ≡ (neck-e₁ (neck⋆ e f {ρ≥1 ρ≡r})) × (neck-e₂ nck) ≢ (neck-e₂ (neck⋆ e f {ρ≥1 ρ≡r}))) × e ≢ (neck-e₂ nck))
  bij₂ {e} {f} {._} refl {≥1} {<predn} = Σ↔ Iid
                             (λ {x} →
                                record
                                { to = record { _⟨$⟩_ = to {x} ; cong = cong (to {x}) }
                                ; from = record { _⟨$⟩_ = from {x} ; cong = cong (from {x}) }
                                })
    where open Data.Nat.≤-Reasoning
          <n : True (suc (ρ e f) ≤? ⌈ n /2⌉)
          <n = fromWitness (begin
                     suc (ρ e f)
                       ≤⟨ toWitness <predn ⟩
                     ⌈ pred n /2⌉
                       ≤⟨ ⌈n/2⌉-mono (≤⇒pred≤ n n m≤m) ⟩
                     (⌈ n /2⌉ ∎))

          to : {nck : Neck e} → (neck-e₂ nck ≢ e × ρ (neck-e₂ nck) f ≡ (ρ e f)) → ((neck-e₁ nck) ≡
                           (neck-e₁ (neck⋆ e f)) × (neck-e₂ nck) ≢ (neck-e₂ (neck⋆ e f))) × e ≢ (neck-e₂ nck)
          to {nck} (≢e , ρ≡) = (0<ρ<predn/2⁻¹.class-B nck ρ≡ (≢sym ≢e) , (≢sym ≢e))
  
          from : {nck : Neck e} → ((neck-e₁ nck) ≡ (neck-e₁ (neck⋆ e f)) × (neck-e₂ nck) ≢ (neck-e₂ (neck⋆ e f))) ×
                  e ≢ (neck-e₂ nck) → (neck-e₂ nck ≢ e × ρ (neck-e₂ nck) f ≡ (ρ e f))
          from {nck} ((≡e₁⋆ , ≢e₂⋆) , ≢e) = ((≢sym ≢e) , (0<ρ<n/2.class-B-ρ nck ≡e₁⋆ ≢e₂⋆ (≢sym ≢e)))

  bij₃ : ∀ {e f r} → (ρ≡r : ρ e f ≡ r) → {≥1 : True (1 ≤? r)} {<predn : True (suc r ≤? ⌈ (pred n) /2⌉)} →
         K e f (suc r) ↔ Σ (Neck e) (λ nck → (proj₁ nck) ≢ (proj₁ (neck⋆ e f {ρ≥1 ρ≡r})) × e ≢ (neck-e₂ nck))
  bij₃ {e} {f} {._} refl {≥1} {<predn} = Σ↔ Iid
                         (λ {x} →
                            record
                            { to = record { _⟨$⟩_ = to {x} ; cong = cong (to {x}) }
                            ; from = record { _⟨$⟩_ = from {x} ; cong = cong (from {x}) }
                            })
    where open Data.Nat.≤-Reasoning
          <n : True (suc (ρ e f) ≤? ⌈ n /2⌉)
          <n = fromWitness (begin
                     suc (ρ e f)
                       ≤⟨ toWitness <predn ⟩
                     ⌈ pred n /2⌉
                       ≤⟨ ⌈n/2⌉-mono (≤⇒pred≤ n n m≤m) ⟩
                     (⌈ n /2⌉ ∎))
          to : {nck : Neck e} → (neck-e₂ nck ≢ e × ρ (neck-e₂ nck) f ≡ suc (ρ e f)) → (proj₁ nck) ≢ (proj₁ (neck⋆ e f)) × e ≢ (neck-e₂ nck)
          to {nck} (≢e , ρ≡) = ((λ eq → 0<ρ<predn/2⁻¹.class-C nck ≢e ρ≡ (cong el eq)) , ≢sym  ≢e)

          from : {nck : Neck e} → (proj₁ nck) ≢ (proj₁ (neck⋆ e f)) × e ≢ (neck-e₂ nck) → (neck-e₂ nck ≢ e × ρ (neck-e₂ nck) f ≡ suc (ρ e f))
          from {nck} (≢e₁⋆ , ≢e)  = (≢sym  ≢e , (0<ρ<n/2.class-C₀-ρ nck (λ eq → ≢e₁⋆ (Σ'≡ eq)) (≢sym ≢e) (toWitness <predn)))


  predn-≥1 : ∀ {e f} → ρ e f ≡ ⌈ (pred (n)) /2⌉ → ρ e f ≥ 1
  predn-≥1 {e} {f} ≡predn = (begin 1 ≤⟨ s≤s z≤n ⟩ ⌈ pred n /2⌉ ≡⟨ sym ≡predn ⟩ (ρ e f ∎))
    where open Data.Nat.≤-Reasoning

  bij₄ : ∀ {e f r} → (ρ≡r : ρ e f ≡ r) {≡predn/2 : True (r ℕ≟ ⌈ (pred (n)) /2⌉)} {oddn : Odd n} →
          K e f r ↔ Σ (Neck e) (λ nck → nck ≢ (neck⋆ e f {fromWitness (predn-≥1 (trans ρ≡r (toWitness ≡predn/2)))} ) × (neck-e₂ nck) ≢ e)
  bij₄ {e} {f} {._} refl {≡predn} {oddn} = Σ↔ Iid (λ {x} →
                                                       record
                                                       { to = record { _⟨$⟩_ = to {x} ; cong = cong (to {x}) }
                                                       ; from = record { _⟨$⟩_ = from {x} ; cong = cong (from {x}) }
                                                       })
    where open Data.Nat.≤-Reasoning
          ≥1 : True (1 ≤? ρ e f )
          ≥1 = fromWitness (begin 1 ≤⟨ s≤s z≤n ⟩ ⌈ pred n /2⌉ ≡⟨ sym (toWitness ≡predn) ⟩ (ρ e f ∎))

          <n : True (suc (ρ e f) ≤? ⌈ n /2⌉)
          <n = fromWitness (begin suc (ρ e f) ≡⟨ cong suc (toWitness ≡predn) ⟩ suc ⌈ pred n /2⌉ ≡⟨ cong suc (helper oddn) ⟩ suc (pred ⌈ n /2⌉) ≡⟨ refl ⟩ (⌈ n /2⌉ ∎))
             where helper : ∀ {x} → Odd x → ⌈ pred x /2⌉ ≡ pred ⌈ x /2⌉
                   helper {zero} ox = refl
                   helper {suc zero} ox = refl
                   helper {suc (suc m)} (oddSuc ox) = sym (lem-even⇒⌊≡⌋ (oddEven ox))

          to : {x : Neck e} → (neck-e₂ x ≢ e × ρ (neck-e₂ x) f ≡ ρ e f) →
                              (x ≢ neck⋆ e f {≥1} × neck-e₂ x ≢ e)
          to {nck} proof = (λ eq → ρ≡1/2-predn⁻¹.class-B {ρ≡ = ≡predn} nck (proj₂ proof) (≢sym (proj₁ proof)) (cong neck-e₂ eq)) , (proj₁ proof) 

          from : {x : Neck e} → (x ≢ neck⋆ e f {≥1} × neck-e₂ x ≢ e) → (neck-e₂ x ≢ e × ρ (neck-e₂ x) f ≡ ρ e f)
          from {nck} proof with pt (neck-e₂ nck) ≟ pt (neck-e₂ (neck⋆ e f ))
          from {nck} proof | yes p = ⊥-elim (proj₁ proof (neck! {nck = nck} {nck' = neck⋆ e f } (≢sym $ proj₂ proof) (pt-inj p)))
          from {nck} proof | no ¬p with ln (neck-e₁ nck) ≟ ln (neck-e₁ (neck⋆ e f))
          from {nck} proof | no ¬p | yes p = (proj₂ proof) , (0<ρ<n/2.class-B-ρ nck (ln-inj p) (λ eq → ¬p (cong pt eq)) ((proj₂ proof)))
          from {nck} proof | no ¬p | no ¬p₁ = (proj₂ proof) , (0<ρ<n/2.class-C₁-ρ nck (λ eq → ¬p₁ (cong ln eq)) (λ eq → ¬p (cong pt eq)) ((proj₂ proof)) (toWitness ≡predn))
        
    
  bij₅ : ∀ {e f r} → (ρ≡r : ρ e f ≡ r) {≡predn/2 : True (r ℕ≟ ⌈ n /2⌉)} {evenn : Even n} →
          K e f (pred r) ↔ (Σ (Neck e) (λ nck → (neck-e₂ nck) ≡ ρ≡n/2.e₂⋆ {n-even = evenn } {≡n/2 = fromWitness (trans ρ≡r (toWitness ≡predn/2))} (proj₁ nck)))
  bij₅ {e} {f} {._} refl {≡predn} {n-even} = Σ↔ Iid (λ {x} → record
                                                               { to = record { _⟨$⟩_ = to {x} ; cong = cong (to {x}) }
                                                               ; from = record { _⟨$⟩_ = from {x} ; cong = cong (from {x}) }
                                                               })
    where        
          to : {x : Neck e} → (neck-e₂ x ≢ e × ρ (neck-e₂ x) f ≡ pred (ρ e f)) → neck-e₂ x ≡ ρ≡n/2.e₂⋆ {n-even = n-even} (proj₁ x)
          to {x} proof = ρ≡n/2⁻¹.class-A₀ {n-even = n-even} x (trans (proj₂ proof) (cong pred (toWitness ≡predn)))

          from : {x : Neck e} → neck-e₂ x ≡ ρ≡n/2.e₂⋆ {n-even = n-even} (proj₁ x) → (neck-e₂ x ≢ e × ρ (neck-e₂ x) f ≡ pred (ρ e f))
          from {x} proof = (λ eq → ρ≡n/2.lem-e₂⋆ {n-even = n-even} {≡n/2 = ≡predn} {l#e = proj₁ x} (trans (sym proof) eq)) , (trans (ρ≡n/2.class-A₀-ρ {n-even = n-even} {≡n/2 = ≡predn} x proof) (sym $ cong pred (toWitness ≡predn)))

     
  bij₆ : ∀ {e f r} → (ρ≡r : ρ e f ≡ r) {≡predn/2 : True (r ℕ≟ ⌈ n /2⌉)} {evenn : Even n} →
          K e f r ↔ (Σ (Neck e)
                              (λ nck → (neck-e₂ nck) ≢ ρ≡n/2.e₂⋆
                                 {n-even = evenn }
                                 {≡n/2 = fromWitness (trans ρ≡r (toWitness ≡predn/2))}
                              (proj₁ nck) × (neck-e₂ nck) ≢ e))
  bij₆ {e} {f} {._} refl {≡predn} {n-even} = Σ↔ Iid (λ {x} → record
                                                               { to = record { _⟨$⟩_ = to {x} ; cong = cong (to {x}) }
                                                               ; from = record { _⟨$⟩_ = from {x} ; cong = cong (from {x}) }
                                                               })
    where to : {x : Neck e} → (neck-e₂ x ≢ e × ρ (neck-e₂ x) f ≡ ρ e f) →
               (neck-e₂ x) ≢ ρ≡n/2.e₂⋆  {n-even = n-even} (proj₁ x) × neck-e₂ x ≢ e
          to {x} proof = (ρ≡n/2⁻¹.class-A₁ {n-even = n-even} x (trans (proj₂ proof) (toWitness ≡predn))) , (proj₁ proof)

          from : {x : Neck e} → (neck-e₂ x) ≢ ρ≡n/2.e₂⋆  {n-even = n-even} (proj₁ x) × neck-e₂ x ≢ e →
                  (neck-e₂ x ≢ e × ρ (neck-e₂ x) f ≡ ρ e f)
          from {x} proof = (proj₂ proof) , (trans (ρ≡n/2.class-A₁-ρ  {n-even = n-even} x (proj₁ proof)) (sym (toWitness ≡predn)))
              

  bij₀ : ∀ {e f} → ρ e f ≡ 0 → K e f 1 ↔ (Σ (Neck e) (λ nck → (neck-e₂ nck) ≢ e))
  bij₀ {e} ρ≡0 rewrite (sym $ ρ≡0⇒e≡f ρ≡0) = Σ↔ Iid  (λ {x} → record
                                                               { to = record { _⟨$⟩_ = to {x} ; cong = cong (to {x}) }
                                                               ; from = record { _⟨$⟩_ = from {x} ; cong = cong (from {x}) }
                                                               })
    where to : {x : Neck e} → (neck-e₂ x ≢ e × ρ (neck-e₂ x) e ≡ 1) → neck-e₂ x ≢ e
          to {x} proof = proj₁ proof
    
          from : {x : Neck e} → neck-e₂ x ≢ e → (neck-e₂ x ≢ e × ρ (neck-e₂ x) e ≡ 1)
          from {x} proof = proof , ρe₂e≡1
            where e₂ = proj₂ x
                  e₁ = proj₁ x

                  x≤1⇒x≡0or1 : ∀ {x} → x ≤ 1 → (x ≡ 0) ⊎ (x ≡ 1)
                  x≤1⇒x≡0or1 z≤n = inj₁ refl
                  x≤1⇒x≡0or1 (s≤s z≤n) = inj₂ refl
  
                  ρe₂e≤1 : ρ (el e₂) e ≤ 1
                  ρe₂e≤1 = sppc-ρ-shorter-than ((el e₂) ∶⟨ (el e₁) ⟩∶ [ e ]) {{T#sym (pf e₂)}} {{T#sym (pf e₁)}}

                  ρe₂e≡1 : ρ (el e₂) e ≡ 1
                  ρe₂e≡1 with x≤1⇒x≡0or1 (ρe₂e≤1)
                  ρe₂e≡1 | inj₁ x≡0 = ⊥-elim (proof (ρ≡0⇒e≡f x≡0))
                  ρe₂e≡1 | inj₂ x≡1 = x≡1
                              
