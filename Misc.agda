open import Data.Nat
open import Data.Empty
open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality as PropEq

module Misc where

  ≤-≥⇒≡ : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
  ≤-≥⇒≡ z≤n z≤n = refl
  ≤-≥⇒≡ (s≤s p) (s≤s q) = cong suc (≤-≥⇒≡ p q)

  ≯⇒≤ : ∀ {x y} → x ≯ y → x ≤ y
  ≯⇒≤ {zero} {zero} p = z≤n
  ≯⇒≤ {zero} {suc y} p = z≤n
  ≯⇒≤ {suc x} {zero} p = ⊥-elim (p (s≤s z≤n))
  ≯⇒≤ {suc x} {suc y} p = s≤s (≯⇒≤ (λ a → p (s≤s a)))

  ≤⇒≯ : ∀ {x y} → x ≤ y → x ≯ y
  ≤⇒≯ z≤n ()
  ≤⇒≯ (s≤s p) q = ≤⇒≯ p (pred-mono q)

  ≡⇒≤ : ∀ {x y} → x ≡ y → x ≤ y
  ≡⇒≤ {x} refl = n∸m≤n zero x
