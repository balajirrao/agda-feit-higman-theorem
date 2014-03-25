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

open import Data.Vec

open import Misc

module FinBijections where
  
  postulate
    prod-bij : ∀ {a b} → Inverse (PropEq.setoid (Fin a × Fin b)) (finSetoid (a * b))
{-
    bij-such-that : {X : Set} → (x y : X) → Inverse (PropEq.setoid X) (PropEq.setoid X)
    lem-bij-such-that : ∀ {X} → (x y : X) →
                         Inverse.to (bij-such-that x y) ⟨$⟩ x ≡ y -}

    fin-exclude : ∀ {a} → ( x : Fin (suc a)) → Inverse (PropEq.setoid (Σ (Fin (suc a)) (λ x₁ → x₁ ≢ x))) (finSetoid a)

    fin-exclude₂ : ∀ {a} → (x y : Fin (suc (suc a))) → x ≢ y → Inverse (PropEq.setoid (Σ (Fin (suc (suc a))) (λ x₁ → x₁ ≢ x × x₁ ≢ y))) (finSetoid a)

    fin-one : ∀ {A : Set} → (x : A) → Σ A (λ x₁ → x₁ ≡ x) ↔ Fin 1

 -- rotl : ∀ {a} → Fin (suc a) → Fin (suc a)

 -- rotl {a} zero = fromℕ a
 -- rotl (suc x) = fromℕ≤ (toℕ (inject₁ x))

  --rotln : ∀ {a} → ℕ → Fin (suc a) → Fin (suc a)
 -- rotln zero = id
 -- rotln (suc m) = rotln m ∘ rotl

 -- →zero : ∀ {a} (x : Fin (suc a)) → Fin (suc a) → Fin (suc a)
 -- →zero x = rotln (toℕ x)
{-
  F : ∀ {a} (i : Fin (suc (suc a))) → toℕ (pred i) N< (suc a)
  F {zero} zero = s≤s z≤n
  F {zero} (suc zero) = m≤m {1}
  F {zero} (suc (suc ()))
  F {suc a} zero = s≤s z≤n
  F {suc a} (suc i) rewrite inject₁-lemma i = prop-toℕ-≤ (suc i)

  G : ∀ {a} (x : Fin (suc (suc a))) → Σ (Fin (suc (suc a))) (λ x₁ → x ≢ x₁) → Fin (suc a)
  G x (proj₁ , proj₂) with compare proj₁ x
  G x (.(inject least) , proj₂) | less .x least = inject! least
  G x (.x , proj₂) | equal .x = ⊥-elim (proj₂ refl)
  G .(inject least) (greatest , proj₂) | greater .greatest least = inject! least


  H : ∀ {a} (x : Fin (suc (suc a))) →  Fin (suc a)  → Σ (Fin (suc (suc a))) (λ x₁ → x ≢ x₁)
  H x y with (inject₁ y) | compare (inject₁ y) x
  H x y | .(inject least) | less .x least = (inject least) , (λ x₁ → {!inject-lemma least!})
  H x y | .x | equal .x = x , {!!}
  H .(inject least) y | greatest | greater .greatest least = greatest , (λ x → {!!})

  exclude : ∀ {a} (x : Fin (2 N+ a)) → Fin (2 N+ a) → Fin (1 N+ a)
  exclude {a} x y = {! fromℕ≤ (toℕ!}

  -}

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
