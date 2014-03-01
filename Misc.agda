open import Data.Nat
open import Data.Empty
open import Data.Nat.Properties

open import Data.Bool

open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import Relation.Binary.PropositionalEquality as PropEq

open SemiringSolver

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

  m≤m : ∀ {m} → m ≤ m
  m≤m = ≡⇒≤ refl

  suc∘pred : ∀ {x} {{≥1 : True (1 ≤? x)}} → suc (pred (x)) ≡ x
  suc∘pred {zero} = λ {{}}
  suc∘pred {suc x} = refl

  module EvenOdd where
    data Even : ℕ → Set
    data Odd : ℕ → Set 

    data Even where
      evenZero : Even 0
      evenSuc : ∀ {m} → Even m → Even (suc (suc m))
  
    data Odd where
      oddOne : Odd 1
      oddSuc : ∀ {m} → Odd m → Odd (suc (suc m))
     
    evenOdd : {n : ℕ} → Even n → Odd (suc n)
    evenOdd evenZero = oddOne
    evenOdd (evenSuc p) = oddSuc (evenOdd p)

    oddEven : {n : ℕ} → Odd n → Even (suc n)
    oddEven oddOne = evenSuc evenZero
    oddEven (oddSuc p) = evenSuc (oddEven p)

  open EvenOdd public

  lem-2x⌈n/2⌉ : ∀ {x} → 2 * ⌈ x /2⌉ ≤ suc x
  lem-2x⌈n/2⌉ {zero} = z≤n
  lem-2x⌈n/2⌉ {suc zero} = s≤s (s≤s z≤n)
  lem-2x⌈n/2⌉ {suc (suc x)} rewrite
    (solve 1 (λ y → (con 1 :+ y) :+ (con 1 :+ (y :+ con 0)) :=
                    con 2 :+ y :+ (y :+ con 0))) refl ⌈ x /2⌉
                                     = (m≤m {2}) +-mono lem-2x⌈n/2⌉ {x}

