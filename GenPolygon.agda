open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties
open Data.Nat.≤-Reasoning

open import Data.Product
open import Data.Empty
open import Data.Unit hiding (_≤_; _≤?_; setoid; _≟_)

open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import Data.Bool hiding (_≟_)

open import Relation.Binary.PropositionalEquality as PropEq

open import Function.Inverse

open import Data.Fin using (Fin)
open import Misc

module GenPolygon where
  open import IncidenceGeometry public

  postulate
    nn : ℕ

  -- Define n so that n > 2
  n : ℕ
  n = suc (suc (suc nn))

  n>2 : n > 2
  n>2 = s≤s (s≤s (s≤s z≤n))
  
  -- Incidence Plane Axioms
  postulate
    IP-pt : {e f : P} → .(False ((pt e) ≟ (pt f))) → .(True ((pt e) #? (pt f))) → ⊥
    IP-ln : {e f : L} → .(False ((ln e) ≟ (ln f))) → .(True ((ln e) #? (ln f))) → ⊥
  
  -- A₁ : There exists a chain of length at most n from e to f
  -- A₂ : There exists at most one irreducible chain of length less than n from e to f
  postulate
    A₁ : (e f : X) → ∃ (λ (c : chain e f) → len c ≤ n)
    A₂ : ∀ {e f} (c c' : Σ' (chain e f) (λ z → len z < n × irred z)) → c ≡ c'
 
  -- From the A₁ postulate it follows that -- TODO : prove it ?
  postulate
    sc : (e f : X) → chain e f

  lambda : (e f : X) → ℕ
  lambda e f = len (sc e f)

  -- A chain is shortest if it's length is lambda
  _is-shortest : ∀ {e f} → (c : chain e f) → Set
  _is-shortest {e} {f} c = len c ≡ lambda e f

  postulate
    sc-shortest : ∀ {e f} → (sc e f) is-shortest

    -- sc is shorter than any given chain
    sc-is-shorter-than_ : ∀ {e f} (c : chain e f) → lambda e f ≤ len c
  
  -- A₁ imples that the shortest length between any two elements can't be more than n
  A₁' : ∀ {e f} → (lambda e f) ≤ n
  A₁' {e} {f} with sc-is-shorter-than (proj₁ (A₁ e f)) | proj₂ (A₁ e f)
  A₁' {e} {f} | a | b = begin len (sc e f) ≤⟨ a ⟩ len (proj₁ (A₁ e f)) ≤⟨ b ⟩ n  ∎

  -- Set of all lines incident with a given point.
  L# : (p : P) → Set
  L# p = Σ' L (λ l → True (pt p #? ln l))
   
  P# : (l : L) → Set
  P# l = Σ' P (λ p → True (ln l #? pt p))

  -- Axioms for Generalized Polygon
  postulate
    ss t : ℕ

  s = (suc ss)

  postulate
    GP-P : (l : L) → Inverse (setoid (P# l)) (setoid (Fin (1 + s)))
    GP-L : (p : P) → Inverse (setoid (L# p)) (setoid (Fin (1 + t)))

  -- Tail of a shortest chain is shortest
  tail-shortest : ∀ {e f} {c : chain e f} → c is-shortest → tail c is-shortest
  tail-shortest {.f} {f} {[ .f ]} cis = cis
  tail-shortest {e} {f} {.e ∷ c} cis = ≤-≥⇒≡ helper (sc-is-shorter-than c)
    where
      helper : (lambda (head c) f) ≥  len c
      helper = pred-mono
               (begin suc (len c)
                          ≡⟨ cis ⟩
                      len (sc e f)
                          ≤⟨ sc-is-shorter-than (e ∷ sc (head c) f) ⟩
                      (suc (len (sc (head c) f)) ∎))

 
  -- shortest chains are irreducible
  shortest-irred : ∀ {e f} (c : chain e f) → c is-shortest → irred c
  shortest-irred {.f} {f} [ .f ] cis = tt
  shortest-irred {e} {f} (_∷_ .e {{e<>f}} {{e#f}} [ .f ]) cis = tt
  shortest-irred {.e} {g} (e ∷ f ∷ c) cis = λ {n} x → ≤⇒≯
                                              (begin _ ≤⟨ s≤s (
                                                sc-is-shorter-than
                                                  proj₁ (short-circuit (_th-segment-of_ n (e ∷ f ∷ c) ) x)) ⟩
                                                _
                                                  ≤⟨ proj₂ (short-circuit (_th-segment-of_ n (e ∷ f ∷ c) ) x) ⟩
                                                _
                                                  ≡⟨ cis ⟩ (len (sc e g) ∎))
                                                (n≤m+n zero _)

  lem-tail-len : ∀ {e f} {c : chain e f} → len (tail c) ≡ pred (len c)
  lem-tail-len {.f} {f} {[ .f ]} = refl
  lem-tail-len {e} {f} {_∷_ .e {{e<>f}} {{e#f}} c} = refl
