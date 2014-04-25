open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties
open Data.Nat.≤-Reasoning

open import Data.Product
open import Data.Empty
open import Data.Unit hiding (_≤_; _≤?_; setoid; _≟_)

open import Relation.Nullary.Core
--open import Relation.Nullary.Decidable

open import Data.Bool hiding (_≟_)

open import Relation.Binary.PropositionalEquality as PropEq

open import Function.Inverse

open import Data.Fin using (Fin)
open import Misc

module GenPolygon where
  open import IncidencePlane public

  postulate
    nn : ℕ

  -- Define n so that n > 2
  n : ℕ
  n = suc (suc (suc nn))

  n>2 : n > 2
  n>2 = s≤s (s≤s (s≤s z≤n))
  
  -- Incidence Plane Axioms
  postulate
    IP-pt : {e f : _} → .(e ≢ f) → .(e # f) → ⊥
  
  -- A₁ : There exists a chain of length at most n from e to f
  -- A₂ : There exists at most one irreducible chain of length less
  --      than n from e to f
  postulate
    A₁ : (e f : X) → ∃ (λ (c : chain e f) → len c ≤ n)
    A₂ : ∀ {e f} (c c' : Σ' (chain e f) (λ z → len z < n × irred z)) → c ≡ c'
  
  -- A₁ imples that the shortest length between any two elements can't be
  -- more than n
  A₁' : ∀ {e f} → (lambda e f) ≤ n
  A₁' {e} {f} with sc-is-shorter-than (proj₁ (A₁ e f)) | proj₂ (A₁ e f)
  A₁' {e} {f} | a | b = begin len (sc e f) ≤⟨ a ⟩
                              len (proj₁ (A₁ e f)) ≤⟨ b ⟩ n  ∎

  -- Set of all lines incident with a given point.
  L# : (p : P) → Set
  L# p = Σ' L (λ l → pt p # ln l)
   
  P# : (l : L) → Set
  P# l = Σ' P (λ p → ln l # pt p)

 
  -- Axioms for Generalized Polygon
  postulate
    ss t : ℕ

  s = (suc ss)

  postulate
    GP-P : (l : L) → (P# l) ↔ Fin (1 + s)
    GP-L : (p : P) → (L# p) ↔ Fin (1 + t)
