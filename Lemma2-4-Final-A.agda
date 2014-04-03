open import Relation.Nullary.Core

open import Relation.Binary.PropositionalEquality as PropEq hiding (proof-irrelevance)

open import Data.Empty
open import Data.Unit hiding (_≤?_; _≤_; _≟_)

open import Data.Product 

open import Data.Bool hiding (_≟_)

open import Data.Nat renaming (_≟_ to _ℕ≟_)
--open Data.Nat.≤-Reasoning

--open import Function.Inverse
open import Data.Sum

open import Data.Nat.Properties
open SemiringSolver

open import Function hiding (_∘_)
open import Function.Equality hiding (_∘_) renaming (cong to Icong)
open import Function.Inverse renaming (sym to Isym; zip to Izip; id to Iid)
open import Function.LeftInverse hiding (_∘_)
import Function.Equivalence as FunEq

open import Function.Bijection hiding (_∘_)

import Data.Fin as F
import Data.Fin.Props as F

open import Function.Related.TypeIsomorphisms

import Relation.Binary.Sigma.Pointwise as SP

import Lemma2-4-Bij-A as bijA
import Lemma2-4-Bij-B as bijB


open import FinBijections

open import Data.Vec hiding ([_])

open import Misc

open import Lemma2-4-Final

module Lemma2-4-Final-A where
  GKL : ∀ {q} → proj₁ (m 0 (1 + q)) ≡ (1 + t) * proj₁ (m 0 q) + (1 + t) * s * proj₁ (m 1 q)
  GKL {q} with q
  ... | a = {!!}


  +-assoc : ∀ {a b c} → a + (b + c) ≡ a + b + c
  +-assoc {x} {y} {z} = solve 3 (λ a b c → a :+ (b :+ c) := a :+ b :+ c) refl x y z

  drop-suc : ∀ {o} {m n : F.Fin o} → F.Fin.suc m ≡ F.suc n → m ≡ n
  drop-suc refl = refl

  tabulate₀ : ∀ {n} → (f : F.Fin n → ℕ) → (∀ w → f w ≡ 0) → sum′ (tabulate f) ≡ 0
  tabulate₀ {zero} f z = refl
  tabulate₀ {suc n} f z rewrite z F.zero = tabulate₀ (λ x → f (F.suc x)) (λ w → z (F.suc w))

  tabulate₁ : ∀ {x n} (a : F.Fin n) → (f : F.Fin n → ℕ) → (f a ≡ x ) → (∀ w → w ≢ a → f w ≡ 0) → sum′ (tabulate f) ≡ x
  tabulate₁ F.zero f refl x₂ = trans (cong (_+_ (f F.zero)) (tabulate₀ (λ x → f (F.suc x)) (λ w → x₂ (F.suc w) (λ ())))) (+-comm {f F.zero} {0})
  tabulate₁ (F.suc a) f x₁ x₂ with x₂ (F.zero) (λ ())
  ... | www rewrite www = tabulate₁ a (λ z → f (F.suc z)) x₁ (λ w x → x₂ (F.suc w) (λ x₃ → x (drop-suc x₃)))

  tabulate₂ : ∀ {x y n} (a b : F.Fin n) (pf₁ : a F.< b) → (f : F.Fin n → ℕ) → (f a ≡ x ) → (f b ≡ y) → (∀ w → w ≢ a → w ≢ b → f w ≡ 0) → sum′ (tabulate f) ≡ x + y
  tabulate₂ F.zero F.zero () d e f g
  tabulate₂ F.zero (F.suc b) (s≤s c) d refl f g = cong (_+_ (d F.zero)) (tabulate₁ b (λ z → d (F.suc z)) f (λ w x → g (F.suc w) (λ ()) (λ x₁ → x (drop-suc x₁))))
  tabulate₂ (F.suc a) F.zero () d e f g
  tabulate₂ (F.suc a) (F.suc b) c d e f g with g (F.zero) (λ ()) (λ ())
  ... | www rewrite www = tabulate₂ a b (pred-mono c) (λ z → d (F.suc z)) e f (λ w x x₁ → g (F.suc w) (λ x₂ → x (drop-suc x₂)) (λ x₂ → x₁ (drop-suc x₂)))
  
  tabulate₃ : ∀ {x y z n} (a b c : F.Fin n) (pf₁ : a F.< b) (pf₂ : b F.< c) → (f : F.Fin n → ℕ) → (f a ≡ x ) → (f b ≡ y) → (f c ≡ z) → (∀ w → w ≢ a → w ≢ b → w ≢ c → f w ≡ 0) → sum′ (tabulate f) ≡ x + y + z 
  tabulate₃ F.zero F.zero F.zero f () w x₁ x₂ x₃ x₄
  tabulate₃ F.zero F.zero (F.suc c) () v w x₁ x₂ x₃ x₄
  tabulate₃ F.zero (F.suc b) F.zero f () w x₁ x₂ x₃ x₄
  tabulate₃ {y = y} {z = z} F.zero (F.suc b) (F.suc c) f v w refl x₂ x₃ x₄ = trans (cong (_+_ (w F.zero)) (tabulate₂ b c (pred-mono v) (λ x → w (F.suc x)) x₂ x₃ (λ w₁ x x₁ → x₄ (F.suc w₁) (λ ()) (λ x₅ → x (drop-suc x₅)) (λ x₅ → x₁ (drop-suc x₅))))) (+-assoc {w F.zero} {y} {z})
  tabulate₃ (F.suc a) F.zero F.zero f () w x₁ x₂ x₃ x₄
  tabulate₃ (F.suc a) F.zero (F.suc c) () (s≤s v) w x₁ x₂ x₃ x₄
  tabulate₃ (F.suc a) (F.suc b) F.zero f () w x₁ x₂ x₃ x₄
  tabulate₃ {x} {y} {z} (F.suc a) (F.suc b) (F.suc c) f v w x₁ x₂ x₃ x₄ with x₄ F.zero (λ ()) (λ ()) (λ ())
  ... | www rewrite www = tabulate₃ {x} {y} {z} a b c (pred-mono f) (pred-mono v)
                            (λ x₅ → w (F.suc x₅)) x₁ x₂ x₃
                            (λ w₁ x₅ x₆ x₇ →
                               x₄ (F.suc w₁) (λ x₈ → x₅ (drop-suc x₈)) (λ x₈ → x₆ (drop-suc x₈))
                               (λ x₈ → x₇ (drop-suc x₈)))

-- --proj₁ (m r q) + (t + s) * proj₁ (m (suc r) q) + t * s * proj₁ (m (2 + r) q)
  GJL : ∀ {r q} → r > 0 → r < ⌈ pred n /2⌉ → proj₁ (m r (1 + q)) ≡ (1 + t) * proj₁ (m r q) + proj₁ (m (pred r) q) + (pred s) * proj₁ (m r q) +  t * s * proj₁ (m (suc r) q)
  GJL {zero} () x₁
  GJL {suc r} {q} x x₁  with ⌊ n /2⌋ ≤? (suc r)
  GJL {suc r} x x₁ | yes p with suc r ℕ≟ ⌊ n /2⌋
  GJL {suc r} x x₁ | yes p₁ | yes p = {!!}
  GJL {suc r} x x₁ | yes p | no ¬p = {!!}
  GJL {suc r} {q} x x₁ | no ¬p = trans (cong (_+_ ((1 + t) * proj₁ (m (suc r) q))) (tabulate₃ {n = suc ⌈ n /2⌉} (F.fromℕ≤ {m = r} helper₀) (F.fromℕ≤ {m = suc r} helper₁) (F.fromℕ≤ {m = 2 + r} helper₂) {!!} {!!} (λ x₂ → {!proj₁ (k r (F.toℕ x₂))!}) {!!} {!!} {!!} {!!})) {!!}
    where open Data.Nat.≤-Reasoning
          helper₀ : r < suc ⌈ n /2⌉
          helper₀ = {!!}

          helper₁ :  suc r < suc ⌈ n /2⌉
          helper₁ = {!!}

          helper₂ : suc (suc r) < suc ⌈ n /2⌉
          helper₂ = {!!}
 
