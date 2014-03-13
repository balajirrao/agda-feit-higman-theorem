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
open import Function.Equality
open import Function.Inverse
open import Data.Sum

open import Data.Nat.Properties
open SemiringSolver

open import Function

open import Misc

module FinBijections where
  
  postulate
    prod-bij : ∀ {a b} → Inverse (PropEq.setoid (Fin (suc a) × Fin (suc b))) (finSetoid ((suc a) * (suc b)))

    bij-such-that : {X : Set} → (x y : X) → Inverse (PropEq.setoid X) (PropEq.setoid X)
    lem-bij-such-that : ∀ {X} → (x y : X) →
                         Inverse.to (bij-such-that x y) ⟨$⟩ x ≡ y 

    fin-exclude : ∀ {a} → ( x : Fin (suc a)) → Inverse (PropEq.setoid (Σ' (Fin (suc a)) (λ x₁ → x₁ ≢ x))) (finSetoid a)

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


  F : ∀ {a b} → Fin a ⊎ Fin b → Fin (a N+ b)
  F {a} {b} (inj₁ x) = inject≤ x (m≤m+n a b)
  F {a} (inj₂ y) = raise a y

  F⁻¹ : ∀ {a b} → Fin (a N+ b) → Fin a ⊎ Fin b
  F⁻¹ {zero} x = inj₂ x
  F⁻¹ {suc a} x with (toℕ x) N≤? a
  F⁻¹ {suc a} x | yes p = inj₁ (fromℕ≤ (s≤s p))
  F⁻¹ {suc a} x | no ¬p = inj₂ (reduce≥ x (≰⇒> ¬p))

  lem₀ : ∀ {a b} (x : Fin (a N+ b)) → (p : toℕ x N< a) → inject≤ (fromℕ≤ p) (m≤m+n a b) ≡ x
  lem₀ {zero} x ()
  lem₀ {suc a} zero (s≤s z≤n) = refl
  lem₀ {suc ._} (suc x) (s≤s (s≤s p)) = cong suc (lem₀ x (s≤s p))
  
  lem₁ : ∀ {a b} (x : Fin (a N+ b)) (p : toℕ x N≥ a) → raise a (reduce≥ x p) ≡ x
  lem₁ {zero} x p = refl
  lem₁ {suc a} zero ()
  lem₁ {suc a} (suc x) (s≤s p) = cong suc (lem₁ x p)

  I : ∀ {a b} (x :  Fin (a N+ b)) →  F {a} {b} ( F⁻¹ x) ≡ x
  I {zero} x = refl
  I {suc a} x with (toℕ x) N≤? a
  I {suc a} x | yes p = lem₀ x (s≤s p)
  I {suc a} x | no ¬p = lem₁ x (≰⇒> ¬p)
  
  reduce-raise : ∀ {a b} → (y : Fin b) (p : toℕ (raise a y) N≥ a) → reduce≥ (raise a y) p ≡ y
  reduce-raise {zero} y p = refl
  reduce-raise {suc a} y (s≤s p) = reduce-raise y p

  J :  ∀ {a b} (x : Fin a ⊎ Fin b) → F⁻¹ {a} {b} (F x) ≡ x
  J {zero} (inj₁ ())
  J {zero} (inj₂ y) = refl
  J {suc a} {b} (inj₁ x) with  toℕ (inject≤ x (s≤s (m≤m+n a b))) N≤? a
  J {suc a} {b} (inj₁ x) | yes p rewrite inject≤-lemma x (m≤m+n (suc a) b) = cong inj₁ (fromℕ≤-toℕ x (s≤s p))
  J {suc a} {b} (inj₁ x) | no ¬p = ⊥-elim (¬p (begin toℕ (inject≤ x (s≤s (m≤m+n a b))) ≡⟨ inject≤-lemma x (m≤m+n (suc a) b) ⟩ toℕ x ≤⟨ prop-toℕ-≤ x ⟩ (a ∎)))
  J {suc a} (inj₂ y) with suc (toℕ (raise a y)) N≤? a
  J {suc a} (inj₂ y) | yes p  rewrite (toℕ-raise a y) = ⊥-elim (helper {a} {toℕ y} p)
    where helper : ∀ {i j} → 1 N+ i N+ j N≤ i → ⊥
          helper {zero} ()
          helper {suc i} (s≤s x) = ⊥-elim (helper x)
  J {suc a} (inj₂ y) | no ¬p with ≰⇒> ¬p
  J {suc a} (inj₂ y) | no ¬p | s≤s k = cong inj₂ (reduce-raise y k)
    

-}
