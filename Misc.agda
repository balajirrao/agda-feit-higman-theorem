open import Data.Nat
open import Data.Empty
open import Data.Nat.Properties

open import Data.Bool

open import Relation.Binary

open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import Relation.Binary.PropositionalEquality as PropEq

open import Data.Product 

import Data.Fin as F
import Data.Fin.Props as F

open import Function 
open import Function.Equality hiding (_∘_; setoid) renaming (cong to Icong)
open import Function.Inverse renaming (sym to Isym; zip to Izip; _∘_ to _I∘_)
open import Function.LeftInverse hiding (_∘_)

open import Function.Related.TypeIsomorphisms

import Relation.Binary.Sigma.Pointwise as SP

open SemiringSolver

import Level 
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

    oddEvenEither : ∀ {x} → Even x → Odd x → ⊥
    oddEvenEither evenZero ()
    oddEvenEither (evenSuc p) (oddSuc x) = oddEvenEither p x

    data Parity (k : ℕ) : Set where
      isEven : Even k → Parity k
      isOdd : Odd k → Parity k

    parity : (k : ℕ) → Parity k
    parity zero = isEven evenZero
    parity (suc k) with parity k
    parity (suc k) | isEven x = isOdd (evenOdd x)
    parity (suc k) | isOdd x = isEven (oddEven x)

    lem-2x⌈n/2⌉-even : ∀ {x} → Even x → 2 * ⌈ x /2⌉ ≡ x
    lem-2x⌈n/2⌉-even {zero} ex = refl
    lem-2x⌈n/2⌉-even {suc zero} ()
    lem-2x⌈n/2⌉-even {suc (suc x)} (evenSuc ex)
                     rewrite solve 1
                       (λ y → con 1 :+ (y :+ (con 1 :+ y :+ con 0)) :=
                          (con 2 :+ y :+ (y :+ con 0))) refl (⌊ suc x /2⌋) =
                                         cong (suc ∘ suc) (lem-2x⌈n/2⌉-even ex)

    lem-even⇒⌊≡⌋ : ∀ {m} → Even m → ⌊ m /2⌋ ≡ ⌈ m /2⌉
    lem-even⇒⌊≡⌋ {zero} em = refl
    lem-even⇒⌊≡⌋ {suc zero} ()
    lem-even⇒⌊≡⌋ {suc (suc m)} (evenSuc em) = cong suc (lem-even⇒⌊≡⌋ em)

  open EvenOdd public

  lem-2x⌈n/2⌉ : ∀ {x} → 2 * ⌈ x /2⌉ ≤ suc x
  lem-2x⌈n/2⌉ {zero} = z≤n
  lem-2x⌈n/2⌉ {suc zero} = s≤s (s≤s z≤n)
  lem-2x⌈n/2⌉ {suc (suc x)} rewrite
    (solve 1 (λ y → (con 1 :+ y) :+ (con 1 :+ (y :+ con 0)) :=
                    con 2 :+ y :+ (y :+ con 0))) refl ⌈ x /2⌉
                                     = (m≤m {2}) +-mono lem-2x⌈n/2⌉ {x}

  record Σ' (A : Set) (P : A → Set) : Set where
    constructor _∶_
    field
      el : A
      .pf  : P el
  open Σ' public

  Σ'≡ : ∀ {A P} → {x y : Σ' A P} → el x ≡ el y → x ≡ y
  Σ'≡ {_} {_} {el ∶ pf} {.el ∶ pf₁} refl = refl

  ΣS : (A : Set) (P : A → Set) → Setoid _ _
  ΣS A P = record { Carrier = Σ A P ; _≈_ = λ x y → proj₁ x ≡ proj₁ y ;
                     isEquivalence = record
                       { refl = refl ; sym = sym ; trans = trans } }
  
  _≈_ : {A : Set} {P : A → Set} → Rel (Σ A P) Level.zero
  _≈_ {A} {P} = Setoid._≈_ (ΣS A P)
  
 -- _⇔_ : ∀ {A A'} (P : A → Set) (P' : A' → Set) → Set
 -- P ⇔ P' = Inverse (ΣS _ P) (ΣS _ P')

  ≤-≢⇒< : ∀ {x y} → x ≤ y → x ≢ y → x < y
  ≤-≢⇒< {zero} {zero} z≤n q = ⊥-elim (q refl)
  ≤-≢⇒< {zero} {suc y} z≤n q = s≤s z≤n
  ≤-≢⇒< {suc x} {zero} () q
  ≤-≢⇒< {suc x} {suc y} (s≤s p) q = s≤s (≤-≢⇒< p (λ x₁ → q (cong suc x₁)))

  +-comm : ∀ {x y} → x + y ≡ y + x
  +-comm {x} {y} = solve 2 (λ x₁ x₂ → x₁ :+ x₂ := x₂ :+ x₁) refl x y

  <1⇒≡0  : ∀ {m} → 1 > m → m ≡ 0
  <1⇒≡0 {zero} x = refl
  <1⇒≡0 {suc m} (s≤s ())

  ¬<-≡ : ∀ {x y} → x < y → x ≡ y  → ⊥
  ¬<-≡ {zero} () refl
  ¬<-≡ {suc x} q refl = ¬<-≡ (pred-mono q) refl


  ≥1-fin-pred : ∀ {a}  {x : F.Fin a} → (F.toℕ x) ≥ 1 → F.toℕ (F.pred x) ≡ pred (F.toℕ x)
  ≥1-fin-pred {zero} {()} p
  ≥1-fin-pred {suc a} {F.zero} ()
  ≥1-fin-pred {suc a} {F.suc x} p = F.inject₁-lemma x

  ≡pred⇒zero : ∀ {x} → x ≡ pred x → x ≡ 0
  ≡pred⇒zero {zero} refl = refl
  ≡pred⇒zero {suc x} ()

  ≡suc⇒⊥ : ∀ {x} → suc x ≡ x → ⊥
  ≡suc⇒⊥ ()

  ≢sym : ∀ {A : Set} {x y : A} → x ≢ y → y ≢ x
  ≢sym neq = λ eq → neq (sym eq)

  ⌊≤⌉ : ∀ x → ⌊ x /2⌋ ≤ ⌈ x /2⌉
  ⌊≤⌉ zero = z≤n
  ⌊≤⌉ (suc zero) = z≤n
  ⌊≤⌉ (suc (suc x)) = s≤s (⌊≤⌉ x)

  lem-fin-subst : ∀ { a b } (x : F.Fin a) → (eq : a ≡ b) → F.toℕ (subst F.Fin eq x) ≡ F.toℕ x
  lem-fin-subst x refl = refl

  cong-pred-suc : ∀ {a b} → {x : a ≡ b} → cong pred (cong suc x) ≡ x
  cong-pred-suc {x = refl} = refl
