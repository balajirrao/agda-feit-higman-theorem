open import Data.Nat
open import Data.Nat.Properties
open Data.Nat.≤-Reasoning

open import Data.Product
open import Data.Empty
open import Data.Unit hiding (_≤_; _≤?_; setoid)

open import Relation.Nullary.Decidable


open import Relation.Binary.PropositionalEquality as PropEq

open import Function.Inverse

open import Data.Fin using (Fin)
open import Misc

module GenPolygon where
  open import IncidenceGeometry public

  postulate
    _n : ℕ

  -- Define n so that n > 2
  n : ℕ
  n = suc (suc (suc _n))

  n>2 : n > 2
  n>2 = s≤s (s≤s (s≤s z≤n))
    
  -- A₁ : There exists a chain of length at most n from e to f
  -- A₂ : There exists at most one irreducible chain of length less than n from e to f
  postulate
    A₁ : (e f : O) → ∃ (λ (c : chain e f) → len c ≤ n)
    A₂ : ∀ {e f} (c c' : ∃ (λ (c : chain e f) → len c < n)) → (proj₁ c) ≡ (proj₁ c')
 
  -- From the A₁ postulate it follows that -- TODO : prove it ?
  postulate
    sc : (e f : O) → chain e f

  lambda : (e f : O) → ℕ
  lambda e f = len (sc e f)

  _is-shortest : ∀ {e f} → (c : chain e f) → Set
  _is-shortest {e} {f} c = len c ≡ lambda e f

  postulate
    sc-shortest : ∀ {e f} → (sc e f) is-shortest
    sc-is-shorter-than_ : ∀ {e f} (c : chain e f) → lambda e f ≤ len c
  

  -- A₁ imples that the shortest length between any two elements can't be more than n
  A₁' : ∀ {e f} → (lambda e f) ≤ n
  A₁' {e} {f} with sc-is-shorter-than (proj₁ (A₁ e f)) | proj₂ (A₁ e f)
  A₁' {e} {f} | a | b = begin len (sc e f) ≤⟨ a ⟩ len (proj₁ (A₁ e f)) ≤⟨ b ⟩ n  ∎

  -- Set of all lines incident with a given point.
  record L# (p : P) : Set where
    constructor _⟦_⟧
    field
      #l : L
      .p#l : (pt p) # (ln #l)
  open L# public

  -- Set of all points incident with a given line.
  record P# (l : L) : Set where
    constructor _⟦_⟧
    field
      #p : P
      .l#p : (ln l) # (pt #p)
  open P# public

  postulate
    s t : ℕ
    GP-P# : (l : L) → Inverse (setoid (P# l)) (setoid (Fin (s + 1)))
    GP-L# : (p : P) → Inverse (setoid (L# p)) (setoid (Fin (t + 1)))

  tail-shortest : ∀ {e f} {c : chain e f} → {≥1 : True (1 ≤? len c) } → c is-shortest → tail c {≥1} is-shortest
  tail-shortest {.f} {f} {[ .f ]} {()} _
  tail-shortest {e} {f} {.e ∷ c} cis = ≤-≥⇒≡ helper (sc-is-shorter-than c)
    where
      helper : (lambda (head c) f) ≥  len c
      helper = pred-mono
               (begin suc (len c)
                          ≡⟨ cis ⟩
                      len (sc e f)
                          ≤⟨ sc-is-shorter-than (e ∷ sc (head c) f) ⟩
                      (suc (len (sc (head c) f)) ∎))

