open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import Relation.Binary.PropositionalEquality as PropEq hiding (proof-irrelevance)

open import Data.Empty
open import Data.Unit hiding (_≤?_; _≤_; _≟_)

open import Data.Product 

open import Data.Nat hiding (_≟_; compare) renaming ( _+_ to _N+_; _∸_ to _N∸_
           ; _≤_ to _N≤_; _≥_ to _N≥_; _<_ to _N<_; _≤?_ to _N≤?_; pred to Npred)
open Data.Nat.≤-Reasoning
open import Data.Fin
open import Data.Fin.Props renaming (setoid to finSetoid)
open import Function.Equality hiding (_∘_)
open import Function.Inverse renaming (id to Iid; sym to Isym)
open import Data.Sum

open import Data.Nat.Properties
open SemiringSolver

open import Function hiding (_∘_)

open import Data.Vec hiding (reverse)

open import Function.Related.TypeIsomorphisms

open import Misc

import Relation.Binary.Sigma.Pointwise as SP

module FinBijections where

  sum-bij : ∀ {a b} → (Fin a ⊎ Fin b) ↔ Fin (a N+ b)
  sum-bij {a} = record { to = record { _⟨$⟩_ = to ; cong = PropEq.cong to } ; from = record { _⟨$⟩_ = from ; cong = PropEq.cong from } ; inverse-of = record { left-inverse-of = left-inverse-of ; right-inverse-of = right-inverse-of {a} } }
    where to : ∀ {a b} → Fin a ⊎ Fin b → Fin (a N+ b)
          to {a} {b} (inj₁ x) = inject≤ x (m≤m+n a b)
          to {a} (inj₂ y) = raise a y

          from : ∀ {a b} → Fin (a N+ b) → Fin a ⊎ Fin b
          from {zero} x = inj₂ x
          from {suc a} x with (toℕ x) N≤? a
          from {suc a} x | yes p = inj₁ (fromℕ≤ (s≤s p))
          from {suc a} x | no ¬p = inj₂ (reduce≥ x (≰⇒> ¬p))

          lem₀ : ∀ {a b} (x : Fin (a N+ b)) → (p : toℕ x N< a) → inject≤ (fromℕ≤ p) (m≤m+n a b) ≡ x
          lem₀ {zero} x ()
          lem₀ {suc a} zero (s≤s z≤n) = refl
          lem₀ {suc ._} (suc x) (s≤s (s≤s p)) = PropEq.cong suc (lem₀ x (s≤s p))

          lem₁ : ∀ {a b} (x : Fin (a N+ b)) (p : toℕ x N≥ a) → raise a (reduce≥ x p) ≡ x
          lem₁ {zero} x p = refl
          lem₁ {suc a} zero ()
          lem₁ {suc a} (suc x) (s≤s p) = PropEq.cong suc (lem₁ x p)

          right-inverse-of : ∀ {a b} (x :  Fin (a N+ b)) →  to {a} {b} ( from x) ≡ x
          right-inverse-of {zero} x = refl
          right-inverse-of {suc a} x with (toℕ x) N≤? a
          right-inverse-of {suc a} x | yes p = lem₀ x (s≤s p)
          right-inverse-of {suc a} x | no ¬p = lem₁ x (≰⇒> ¬p)

          reduce-raise : ∀ {a b} → (y : Fin b) (p : toℕ (raise a y) N≥ a) → reduce≥ (raise a y) p ≡ y
          reduce-raise {zero} y p = refl
          reduce-raise {suc a} y (s≤s p) = reduce-raise y p

          left-inverse-of :  ∀ {a b} (x : Fin a ⊎ Fin b) → from {a} {b} (to x) ≡ x
          left-inverse-of {zero} (inj₁ ())
          left-inverse-of {zero} (inj₂ y) = refl
          left-inverse-of {suc a} {b} (inj₁ x) with  toℕ (inject≤ x (s≤s (m≤m+n a b))) N≤? a
          left-inverse-of {suc a} {b} (inj₁ x) | yes p rewrite inject≤-lemma x (m≤m+n (suc a) b) = PropEq.cong inj₁ (fromℕ≤-toℕ x (s≤s p))
          left-inverse-of {suc a} {b} (inj₁ x) | no ¬p = ⊥-elim (¬p (begin toℕ (inject≤ x (s≤s (m≤m+n a b))) ≡⟨ inject≤-lemma x (m≤m+n (suc a) b) ⟩ toℕ x ≤⟨ prop-toℕ-≤ x ⟩ (a ∎)))
          left-inverse-of {suc a} (inj₂ y) with suc (toℕ (raise a y)) N≤? a
          left-inverse-of {suc a} (inj₂ y) | yes p  rewrite (toℕ-raise a y) = ⊥-elim (helper {a} {toℕ y} p)
            where helper : ∀ {i j} → 1 N+ i N+ j N≤ i → ⊥
                  helper {zero} ()
                  helper {suc i} (s≤s x) = ⊥-elim (helper x)
          left-inverse-of {suc a} (inj₂ y) | no ¬p with ≰⇒> ¬p
          left-inverse-of {suc a} (inj₂ y) | no ¬p | s≤s k = PropEq.cong inj₂ (reduce-raise y k)
    
  sum′ : ∀ {n} → Vec ℕ n → ℕ
  sum′ {zero} [] = zero
  sum′ {suc n} (x ∷ v) = x N+ sum′ v

  bij-split : ∀ {a} → (g : Fin (suc a) → ℕ) → (Fin (g zero) ⊎ Σ (Fin a) (λ x → Fin (g (suc x))))  ↔ Σ (Fin (suc a)) (λ x → Fin (g x))
  bij-split {a} g = record { to = record { _⟨$⟩_ = from ; cong = PropEq.cong _ } ; from = record { _⟨$⟩_ = to ; cong = PropEq.cong _ } ; inverse-of = record { left-inverse-of = right-inverse-of ; right-inverse-of = left-inverse-of } }
    where to : Σ (Fin (suc a)) (λ x → Fin (g x)) →  Fin (g (zero)) ⊎ Σ (Fin a) (λ x → Fin (g (raise 1 x)))
          to (zero , proj₂) = inj₁ proj₂
          to (suc proj₁ , proj₂) = inj₂ (proj₁ , proj₂)

          from : Fin (g (zero)) ⊎ Σ (Fin a) (λ x → Fin (g (suc x))) → Σ (Fin (suc a)) (λ x → Fin (g x))
          from (inj₂ x) = (suc (proj₁ x)) , (proj₂ x)
          from (inj₁ y) = zero , y

          left-inverse-of : ∀ x → from (to x) ≡ x
          left-inverse-of (zero , proj₂) = refl
          left-inverse-of (suc proj₁ , proj₂) = refl

          right-inverse-of :  ∀ x → to (from x) ≡ x
          right-inverse-of (inj₁ x) = PropEq.cong inj₁ refl
          right-inverse-of (inj₂ y) = refl

  vec-bij-split : ∀ {a} (g : Fin (suc a) → ℕ) → Fin (sum′ {suc a} (tabulate g)) ↔ (Fin (g zero) ⊎ Σ (Fin a) (λ x → Fin (g (suc x))) )
  vec-bij-split {zero} g rewrite (+-comm {g zero} {zero}) = record { to = record { _⟨$⟩_ = to ; cong = PropEq.cong _ } ; from = record { _⟨$⟩_ = from ; cong = PropEq.cong _ } ; inverse-of = record { left-inverse-of = λ x → refl ; right-inverse-of = right-inverse-of } }
    where to : Fin (g zero) →
             Fin (g zero) ⊎ (Σ (Fin zero) (λ x → Fin (g (suc x)))) 
          to = inj₁

          from : Fin (g zero) ⊎ (Σ (Fin zero) (λ x → Fin (g (suc x)))) → Fin (g zero)
          from (inj₂ (() , proj₂))
          from (inj₁ y) = y

          right-inverse-of :  ∀ x → to (from x) ≡ x
          right-inverse-of (inj₂ (() , proj₂))
          right-inverse-of (inj₁ y) = refl
          
  vec-bij-split {suc a} g = bij
    where open import Relation.Binary.Sum
          bij : Fin ((g zero) N+ (sum′ {suc a} (tabulate (λ x → g (suc x))))) ↔ (Fin (g zero) ⊎ Σ (Fin (suc a)) (λ x → Fin (g (suc x))) )
          bij = Iid ⊎-↔ (bij-split (λ x → g (suc x)) ∘ vec-bij-split {a} (λ x → g (suc x))) ∘
                 Isym
                 (sum-bij {g zero} {sum′ {suc a} (tabulate (λ x → g (suc x)))})
             
      
  vec-bij : ∀ {a} (g : Fin (suc a) → ℕ) → Fin (sum′ {suc a} (tabulate g)) ↔ Σ (Fin (suc a)) (λ x → Fin (g x))
  vec-bij {a} g = bij-split g ∘ vec-bij-split g


  fromℕ-bij : {P Q : ℕ → Set} {a : ℕ} → (∀ {x} → P x ↔ Q x) → ({y : Fin a} → P (toℕ y) ↔ Q (toℕ y))
  fromℕ-bij {P} {Q} {a} bij {y} = bij {toℕ y}

  lem-tabulate : ∀ {a b} → sum′ (tabulate {a} (λ _ → b)) ≡ a * b
  lem-tabulate {zero} =  refl
  lem-tabulate {suc a} {b} = PropEq.cong (_N+_ b) (lem-tabulate {a} {b})

  prod-bij : ∀ {a b} → Inverse (PropEq.setoid (Fin a × Fin b)) (finSetoid (a * b))
  prod-bij {zero} {b} = helper
    where to : Fin 0 × Fin b → Fin 0
          to ( () , _)
          
          from : Fin 0 → Fin 0 × Fin b
          from ()

          left-inverse-of : ∀ x → from (to x) ≡ x
          left-inverse-of ( () , _)

          right-inverse-of : ∀ x → to (from x) ≡ x
          right-inverse-of ()

          helper : (Fin 0 × Fin b) ↔ Fin 0
          helper = record
                     { to = record { _⟨$⟩_ = to ; cong = PropEq.cong to }
                     ; from = record { _⟨$⟩_ = from ; cong = PropEq.cong from }
                     ; inverse-of =
                         record
                         { left-inverse-of = left-inverse-of
                         ; right-inverse-of = right-inverse-of
                         }
                     }
          
  prod-bij {suc a} {b} = helper ∘ Isym (vec-bij {a} (λ _ → b))
    where helper :  Fin (sum′ (tabulate {suc a} (λ _ → b))) ↔ Fin ((suc a) * b)
          helper rewrite (lem-tabulate {suc a} {b}) = Iid


  fin-exclude₀ : ∀ {a} → Inverse (PropEq.setoid (Σ (Fin (suc a)) (λ x₁ → x₁ ≢ zero))) (finSetoid a)
  fin-exclude₀ {a} = record
                       { to = record { _⟨$⟩_ = to ; cong = PropEq.cong to }
                       ; from = record { _⟨$⟩_ = from ; cong = PropEq.cong from }
                       ; inverse-of =
                           record { left-inverse-of = left-inverse-of ; right-inverse-of = λ _ → refl }
                       }
    where helper : ∀ {a} {x : Fin (suc a)} → x ≢ zero → toℕ x N≥ 1
          helper {x = zero} x = ⊥-elim (x refl)
          helper {x = suc _} x₁ = s≤s z≤n       
         
          to : Σ (Fin (suc a)) (λ x₁ → x₁ ≢ zero) → Fin a
          to (zero , y) = ⊥-elim (y refl)
          to (suc x , y) = x

          from : Fin a → Σ (Fin (suc a)) (λ x₁ → x₁ ≢ zero)
          from x = (suc x) , (λ ())
          
          left-inverse-of : ∀ x → from (to x) ≡ x
          left-inverse-of (zero , y) = ⊥-elim (y refl)
          left-inverse-of (suc x , y) = Inverse.to Σ-≡,≡↔≡ ⟨$⟩ (refl , ext)
            where postulate ext : {A : Set} {a b : A} {x y : a ≢ b} → x ≡ y
                  
  rotln : ∀ {a} → ℕ → Fin a → Fin a
  rotln {zero} _ ()
  rotln zero x = x
  rotln {suc a} (suc m) zero = rotln m (fromℕ a)
  rotln {suc a} (suc m) (suc x) = inject₁ $ rotln {a} m x

  tozero : ∀ {a} → (x : Fin (suc a)) → Fin (suc a) → Fin (suc a)
  tozero x y with (y ≟ x)
  tozero x y | yes p = zero
  tozero x y | no ¬p with (y ≟ zero)
  tozero x y | no ¬p | yes p = x
  tozero x y | no ¬p₁ | no ¬p = y


  tozero-bij : ∀ {a} → (x : Fin a) → Fin a ↔ Fin a
  tozero-bij {zero} x = Iid
  tozero-bij {suc a} x = record { to = record { _⟨$⟩_ = to ; cong = PropEq.cong to } ; from = record { _⟨$⟩_ = to ; cong = PropEq.cong to } ; inverse-of = record { left-inverse-of = inverse-of ; right-inverse-of = inverse-of } }
    where to = tozero x

          inverse-of : ∀ y → to (to y) ≡ y
          inverse-of y with (to y ≟ x)
          inverse-of y | yes p with y ≟ x
          inverse-of y | yes p₁ | yes p = trans p₁ (sym p)
          inverse-of y | yes p | no ¬p with y ≟ zero
          inverse-of y | yes p₁ | no ¬p | yes p = sym p
          inverse-of y | yes p | no ¬p₁ | no ¬p = ⊥-elim (¬p₁ p)
          inverse-of y | no ¬p with (to y ≟ zero)
          inverse-of y | no ¬p | yes p with y ≟ x
          inverse-of y | no ¬p | yes p₁ | yes p = sym p
          inverse-of y | no ¬p₁ | yes p | no ¬p with y ≟ zero
          inverse-of y | no ¬p₁ | yes p₁ | no ¬p | yes p = ⊥-elim (¬p₁ refl)
          inverse-of y | no ¬p₂ | yes p | no ¬p₁ | no ¬p = ⊥-elim (¬p p)
          inverse-of y | no ¬p₁ | no ¬p with y ≟ x
          inverse-of y | no ¬p₁ | no ¬p | yes p = ⊥-elim (¬p refl)
          inverse-of y | no ¬p₂ | no ¬p₁ | no ¬p with y ≟ zero
          inverse-of y | no ¬p₂ | no ¬p₁ | no ¬p | yes p = ⊥-elim (¬p₂ refl)
          inverse-of y | no ¬p₃ | no ¬p₂ | no ¬p₁ | no ¬p = refl


  lem→zero : ∀ {a} {x : Fin (suc a)} → tozero x x ≡ zero
  lem→zero {x = x} with x ≟ x 
  lem→zero | yes p = refl
  lem→zero | no ¬p = ⊥-elim (¬p refl) 

  fin-exclude′ : ∀ {a} → ( x : Fin (suc a)) → (Σ (Fin (suc a)) (λ x₁ → x₁ ≢ x)) ↔
                          (Σ (Fin (suc a)) (λ x₁ → x₁ ≢ zero))
  fin-exclude′ x = Σ↔ (tozero-bij x) (λ {y} → record { to = record { _⟨$⟩_ = λ x₁ x₂ → x₁ (sym $
                                                                                              Inverse.injective (tozero-bij x)
                                                                                              (trans (lem→zero {x = x}) (sym x₂))) ; cong = PropEq.cong _ } ; from = record { _⟨$⟩_ = λ x₁ x₂ → x₁ (subst (λ z → tozero z y ≡ zero) x₂ (lem→zero {x = y})) ; cong = PropEq.cong _ } })
               where postulate Σ↔ : predicate-irrelevant-Σ↔


  fin-exclude : ∀ {a} → ( x : Fin (suc a)) → Inverse (PropEq.setoid (Σ (Fin (suc a)) (λ x₁ → x₁ ≢ x))) (finSetoid a)
  fin-exclude {a} x = fin-exclude₀ ∘ (fin-exclude′ x)

  fin-exclude₂′ : ∀ {a} (x y : Fin (suc (suc a))) → (Σ (Fin (suc (suc a))) (λ x₁ → x₁ ≢ x × x₁ ≢ y)) ↔ Σ (Σ (Fin (suc (suc a))) (λ x₁ → x₁ ≢ x)) (λ x₁ → proj₁ x₁ ≢ y)
  fin-exclude₂′ x y = record { to = record { _⟨$⟩_ = λ x₁ → ((proj₁ x₁) , (proj₁ $ proj₂ x₁)) , (proj₂ $ proj₂ x₁) ; cong = PropEq.cong _ } ; from = record { _⟨$⟩_ = λ x₁ → (proj₁ $ proj₁ x₁) , ((proj₂ $ proj₁ x₁) , (proj₂ x₁)) ; cong = PropEq.cong _ } ; inverse-of = record { left-inverse-of = λ _ → refl ; right-inverse-of = λ _ → refl } }

  fin-exclude₂″ : ∀ {a} → (x y : Fin (suc (suc a))) → x ≢ y → Σ (Σ (Fin (suc (suc a))) (λ x₁ → x₁ ≢ x)) (λ x₁ → proj₁ x₁ ≢ y) ↔ Fin a
  fin-exclude₂″  {a} x y neq = fin-exclude {a} (Inverse.to (fin-exclude x) ⟨$⟩ (y , ≢sym neq)) ∘ Σ↔ (fin-exclude {suc a} x) (record { to = record { _⟨$⟩_ = to ; cong = PropEq.cong to } ; from = record { _⟨$⟩_ = from ; cong = PropEq.cong from } })
    where postulate Σ↔ : predicate-irrelevant-Σ↔
          to : {x₁ : Σ (Fin (suc (suc a))) (λ x₂ → x₂ ≢ x)} →
               proj₁ x₁ ≢ y → Inverse.to (fin-exclude x) ⟨$⟩ x₁ ≢ Inverse.to (fin-exclude x) ⟨$⟩ (y , (≢sym neq))
          to {x₁} neq₀ = λ eq → neq₀ (PropEq.cong proj₁ $ Inverse.injective (fin-exclude x) eq)

          from : {x₁ : Σ (Fin (suc (suc a))) (λ x₂ → x₂ ≢ x)} → Inverse.to (fin-exclude x) ⟨$⟩ x₁ ≢ Inverse.to (fin-exclude x) ⟨$⟩ (y , (≢sym neq)) → proj₁ x₁ ≢ y
          from {x₁} neq₀ = λ eq → neq₀ (PropEq.cong (_⟨$⟩_ (Inverse.to (fin-exclude x))) (Inverse.to Σ-≡,≡↔≡ ⟨$⟩ (eq , ext)))
             where postulate ext : {A : Set} {a b : A} {x y : a ≢ b} → x ≡ y

  fin-exclude₂ :  ∀ {a} (x y : Fin (suc (suc a))) →  x ≢ y → (Σ (Fin (suc (suc a))) (λ x₁ → x₁ ≢ x × x₁ ≢ y)) ↔ Fin a
  fin-exclude₂ {a} x y neq = (fin-exclude₂″ x y neq) ∘ (fin-exclude₂′ x y)

  fin-one : ∀ {A : Set} → (x : A) → Σ A (λ x₁ → x₁ ≡ x) ↔ Fin 1
  fin-one {A} x = record
                    { to = record { _⟨$⟩_ = to ; cong = PropEq.cong to }
                    ; from = record { _⟨$⟩_ = from ; cong = PropEq.cong from }
                    ; inverse-of =
                        record
                        { left-inverse-of = left-inverse-of
                        ; right-inverse-of = right-inverse-of
                        }
                    }
    where to : Σ A (λ x₁ → x₁ ≡ x) → Fin 1
          to x = zero

          from  : Fin 1 → Σ A (λ x₁ → x₁ ≡ x)
          from y = x , refl

          left-inverse-of : ∀ x → from (to x) ≡ x
          left-inverse-of y = Inverse.to Σ-≡,≡↔≡ ⟨$⟩ ((sym $ proj₂ y) , (PropEq.proof-irrelevance _ _))

          right-inverse-of : ∀ x → to (from x) ≡ x
          right-inverse-of zero = refl
          right-inverse-of (suc ())
