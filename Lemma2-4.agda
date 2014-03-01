open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import Relation.Binary.PropositionalEquality as PropEq hiding (proof-irrelevance)

open import Data.Bool
open import Data.Bool.Properties

open import Data.Empty
open import Data.Unit hiding (_≤?_; _≤_)

open import Data.Product 

open import Data.Nat

open import Data.Nat.Properties
open SemiringSolver

open import Misc

module Lemma2-4 where
  open import Lemma2-4-core public

  neckl : ∀ {e f} (ppc : ppchain e f) {{≥1 : True (1 ≤? ρ' ppc)}} → L# (neckp (ppc))
  neckl {.f} {f} [ .f ] {{()}}
  neckl {e} (_∶⟨_⟩∶_ .e e₁ ppc {{e#e₁}} {{e₁#e₂}}) {{_}} = e₁ , (fromWitness (toWitness e₁#e₂))

  -- In the below two lemmas we prove that to ensure λ < n
  -- we need to ensure ρ < n / 2
  
  lem-ρ-len<n : ∀ {e f} {ppc : ppchain e f} → ρ' ppc < ⌈ n /2⌉ → len (ppc as-c) < n
  lem-ρ-len<n {e} {f} {ppc} p = pred-mono (begin
                      2 + len (ppc as-c)
                        ≡⟨ cong (_+_ 2) lem-2xρ-len ⟩
                      2 + 2 * ρ' ppc
                        ≡⟨ solve 1
                      (λ t₁ →
                        con 2 :+ t₁ :+ (t₁ :+ con 0) :=
                            con 1 :+ t₁ :+ (con 1 :+ t₁ :+ con 0))
                                           refl (ρ' ppc) ⟩
                      2 * (1 + ρ' ppc)
                        ≤⟨ m≤m {2} *-mono p ⟩
                      2 * ⌈ n /2⌉
                        ≤⟨ lem-2x⌈n/2⌉ ⟩
                      (1 + n ∎) )
    where open Data.Nat.≤-Reasoning

  lem-len-ρ<⌈n/2⌉ : ∀ {e f} {ppc : ppchain e f} → len (ppc as-c) < n →  ρ' ppc < ⌈ n /2⌉
  lem-len-ρ<⌈n/2⌉ {e} {f} {ppc} p = begin
                              1 + ρ' ppc
                                ≡⟨ cong suc (sym lem-len/2-ρ) ⟩
                              1 + ⌊ len (ppc as-c) /2⌋
                                ≤⟨ ⌊n/2⌋-mono (s≤s p) ⟩
                              (⌈ n /2⌉ ∎)
    where open Data.Nat.≤-Reasoning

  -- Axiom A₂ in ρ terms, but now with proof
  A₂-ρ : ∀ {e f} (ppc ppc' : ∃ (λ (z : ppchain e f) → ρ' z < ⌈ n /2⌉)) →
                                                 (proj₁ ppc) ≡ (proj₁ ppc')
  A₂-ρ (ppc , p) (ppc' , p') with cong _as-ppc
                                  (A₂ (ppc as-c , lem-ρ-len<n p)
                                  (ppc' as-c , lem-ρ-len<n p'))
  ... | z rewrite lem-id₁ {ppc = ppc} | lem-id₁ {ppc = ppc'} = z

  -- We have three classes of points e₂ A B and C
  module e₂-classes {e f : P} {{≥1 : True (1 ≤? ρ e f)}} {{≤n : True (suc (ρ e f) ≤? ⌈ n /2⌉)}} where
  
    -- second point along the shortest pp chain
    e₂⋆ : P
    e₂⋆ = neckp (sppc e f)

    -- first line along the shortest pp chain
    e₁⋆ : L
    e₁⋆ = #l (neckl (sppc e f))

    record A : Set where
      field
        e₂ : P
        e₂≡e₂⋆ : e₂ ≡ e₂⋆

    record B : Set where
      field
        e₂ : P
        .e₂#e₁⋆ : True ((pt e₂) #? (ln e₁⋆))
        e₂≢e₂⋆ : e₂ ≢ e₂⋆
        .e₂≢e : e₂ ≢ e

    record C : Set where
      field
        e₂ : P
        e₁ : L
        .e#e₁ : True ((pt e) #? (ln e₁))
        .e₁≢e₁⋆ : e₁ ≢ e₁⋆
    

    -- ρ e₂ f ≡ r - 1 for class A
    ρ-A : {x : A} → ρ (A.e₂ x) f ≡ pred (ρ e f)
    ρ-A {x} rewrite (A.e₂≡e₂⋆ x) = trans
                                   (sym (tailpp-ρ-shortest {ppc = sppc e f} refl))
                                   (lem-tailpp-ρ {ppc = sppc e f})
    


    ρ-B₀ : (x : B) → ρ (B.e₂ x) f ≤ ρ e f
    ρ-B₀ x = begin
               ρ e₂ f
                 ≤⟨ sppc-ρ-shorter-than (e₂ ∶⟨ e₁⋆ ⟩∶ sppc e₂⋆ f)
                   {{e₂#e₁⋆}} {{l#p (neckl (sppc e f))}} ⟩
               suc (ρ e₂⋆ f)
                 ≡⟨  cong suc (ρ-A {record { e₂ = e₂⋆; e₂≡e₂⋆ = refl }}) ⟩
               suc (pred (ρ e f))
                 ≡⟨ suc∘pred ⟩
               (ρ e f ∎)
        where open B x
              open Data.Nat.≤-Reasoning

    -- We next show that if ρ e₂ f < ρ e f, we have a contradiction. We construct
    -- a chain e e₁⋆ (sc e₂ f)
    ρ-B-ppc : (x : B) → ppchain e f
    ρ-B-ppc x = (e ∶⟨ e₁⋆ ⟩∶ sppc e₂ f) {{{!!}}} {{fromWitness (#sym (toWitness (e₂#e₁⋆)))}}
            where open B x
    
    -- This chain has ρ' < ⌈ n /2⌉ so that we can invoke A₂
    ρ-B-ppc-≤n/2 : ∀ {x} → ρ (B.e₂ x) f < ρ e f  → (ρ' (ρ-B-ppc x) < ⌈ n /2⌉)
    ρ-B-ppc-≤n/2 {x} l = begin
                           suc (suc (ρ e₂ f)) ≤⟨ s≤s l ⟩
                           suc (ρ e f) ≤⟨ toWitness ≤n ⟩ (⌈ n /2⌉ ∎)
      where open B x
            open Data.Nat.≤-Reasoning

    ρ-B₁ : (x : B) → ρ (B.e₂ x) f < ρ e f → ⊥
    ρ-B₁ x l with (A₂-ρ (ρ-B-ppc x , ρ-B-ppc-≤n/2 {x} l) (sppc e f , toWitness ≤n))
    ... | z = ⊥-elim (B.e₂≢e₂⋆ x (cong neckp z))
    
    ρ-B : {x : B} → ρ (B.e₂ x) f ≡ ρ e f
    ρ-B {x} = ≤-≥⇒≡ (ρ-B₀ x) (pred-mono (≰⇒> (ρ-B₁ x)))
