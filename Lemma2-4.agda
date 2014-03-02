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

  neckl : ∀ {e f} (ppc : ppchain e f) → True (1 ≤? ρ' ppc) →
                                   Subset L (λ l → pt e # ln l × ln l # pt (neckp ppc))
  neckl {.f} {f} [ .f ] ()
  neckl {e} (_∶⟨_⟩∶_ .e e₁ ppc {{e#e₁}} {{e₁#e₂}}) _ =
                           record { elem = e₁; proof = (toWitness e#e₁) , toWitness e₁#e₂ }

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

  A₁-ρ : (e f : P) → ∃ (λ (ppc : ppchain e f) → ρ' ppc ≤ ⌊ n /2⌋)
  A₁-ρ e f = (proj₁ (A₁ (pt e) (pt f))) as-ppc ,
                    (begin
                      ρ' _
                         ≡⟨ sym lem-len/2-ρ ⟩
                      ⌊ len (((proj₁ (A₁ (pt e) (pt f))) as-ppc) as-c) /2⌋
                        ≡⟨ cong ⌊_/2⌋ (cong len (lem-id₀ {c = (proj₁ (A₁ (pt e) (pt f)))})) ⟩
                      ⌊ len (proj₁ (A₁ (pt e) (pt f))) /2⌋
                        ≤⟨ ⌊n/2⌋-mono (proj₂ (A₁ (pt e) (pt f))) ⟩
                      (⌊ n /2⌋ ∎))
         where open Data.Nat.≤-Reasoning
              
  A₁'-ρ : ∀ {e f} → (ρ e f) ≤ ⌊ n /2⌋
  A₁'-ρ {e} {f} with sppc-ρ-shorter-than (proj₁ (A₁-ρ e f)) | proj₂ (A₁-ρ e f)
  A₁'-ρ {e} {f} | a | b = begin ρ' (sppc e f) ≤⟨ a ⟩ ρ' (proj₁ (A₁-ρ e f)) ≤⟨ b ⟩ ⌊ n /2⌋  ∎
        where open Data.Nat.≤-Reasoning
                                
  -- Axiom A₂ in ρ terms, but now with proof
  A₂-ρ : ∀ {e f} (ppc ppc' : ∃ (λ (z : ppchain e f) → ρ' z < ⌈ n /2⌉)) →
                                                 (proj₁ ppc) ≡ (proj₁ ppc')
  A₂-ρ (ppc , p) (ppc' , p') with cong _as-ppc
                                  (A₂ (ppc as-c , lem-ρ-len<n p)
                                  (ppc' as-c , lem-ρ-len<n p'))
  ... | z rewrite lem-id₁ {ppc = ppc} | lem-id₁ {ppc = ppc'} = z

  -- We have three classes of points e₂ A B and C
  module e₂-classes {e f : P} {≥1 : True (1 ≤? ρ e f)} {≤n : True (suc (ρ e f) ≤? ⌈ n /2⌉)} where
  
    -- second point along the shortest pp chain
    e₂⋆ : P
    e₂⋆ = neckp (sppc e f)

    -- first line along the shortest pp chain
    e₁⋆ : L
    e₁⋆ = Subset.elem (neckl (sppc e f) ≥1)

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
        .e#e₁ : True ((ln e₁) #? (pt e) )
        .e₂#e₁ : True ((pt e₂) #? (ln e₁))
        e₁≢e₁⋆ : e₁ ≢ e₁⋆
        e₂≢e : (pt e₂) ≢ (pt e)
    

    -- ρ e₂ f ≡ r - 1 for class A
    ρ-A : {x : A} → ρ (A.e₂ x) f ≡ pred (ρ e f)
    ρ-A {x} rewrite (A.e₂≡e₂⋆ x) = trans
                                   (sym (tailpp-ρ-shortest {ppc = sppc e f} refl))
                                   (lem-tailpp-ρ {ppc = sppc e f})
    

    ρ-B₀ : (x : B) → ρ (B.e₂ x) f ≤ ρ e f
    ρ-B₀ x = begin
               ρ e₂ f
                 ≤⟨ sppc-ρ-shorter-than (e₂ ∶⟨ e₁⋆ ⟩∶ sppc e₂⋆ f)
                   {{e₂#e₁⋆}} {{fromWitness (proj₂ (Subset.proof (neckl (sppc e f) ≥1)))}} ⟩
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
    ρ-B-ppc x = (e ∶⟨ e₁⋆ ⟩∶ sppc e₂ f)
                   {{fromWitness (proj₁ (Subset.proof (neckl (sppc e f) ≥1)))}}
                   {{fromWitness (#sym (toWitness (e₂#e₁⋆)))}}
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

    -- The third class of points e₂
    ρ-C₀ : (x : C) → ρ (C.e₂ x) f ≤ 1 + ρ e f
    ρ-C₀ x = sppc-ρ-shorter-than (e₂ ∶⟨ e₁ ⟩∶ sppc e f)
      where open C x

    ρ-C-c₁ : (x : C) → ρ (C.e₂ x) f ≤ ρ e f → chain (ln (C.e₁ x)) (pt f)
    ρ-C-c₁ x t = _∷_ (ln e₁) {{fromWitnessFalse (λ ())}} {{fromWitness (#sym (toWitness e₂#e₁))}} (sc (pt e₂) (pt f))
      where open C x

    ρ-C-c₂ : (x : C) → chain (ln (C.e₁ x)) (pt f)
    ρ-C-c₂ x = _∷_ (ln e₁) {{fromWitnessFalse (λ ())}} {{e#e₁}} (sc (pt e) (pt f))
      where open C x

    ρ-C-c₂-len : {x : C} → True (suc (ρ e f) ≤? ⌈ (pred (n)) /2⌉ ) → len (ρ-C-c₂ x) < n
    ρ-C-c₂-len {x} ≤pred-n = begin
                             2 + lambda (pt e) (pt f)
                               ≡⟨ cong (_+_ 2) lem-2xρ-lambda ⟩
                             2 + 2 * ρ e f
                               ≡⟨ solve 1 (λ y → con 2 :+ con 2 :* y :=
                                          con 2 :* (con 1 :+ y)) refl
                                     (ρ e f) ⟩               
                             2 * (1 + ρ e f)
                               ≤⟨ m≤m {2} *-mono toWitness ≤pred-n ⟩
                             2 * ⌈ (pred (n)) /2⌉
                               ≤⟨ lem-2x⌈n/2⌉ ⟩
                             n ∎ 
      where open C x
            open Data.Nat.≤-Reasoning

    -- if ρ < (n - 1) / 2
    ρ-C-c₁-len : {x : C} {p : ρ (C.e₂ x) f ≤ ρ e f} → True (suc(ρ e f) ≤? ⌈ (pred (n)) /2⌉ )→ len (ρ-C-c₁ x p) < n
    ρ-C-c₁-len {x} {p} ≤pred-n = begin 2 + lambda (pt e₂) (pt f) ≤⟨ s≤s (s≤s helper) ⟩ 2 + lambda (pt e) (pt f) ≤⟨ (ρ-C-c₂-len {x}) ≤pred-n ⟩ (n ∎)
      where open C x
            
            helper : lambda (pt e₂) (pt f) ≤ lambda (pt e) (pt f)
            helper rewrite lem-2xρ-lambda {e₂} {f} | lem-2xρ-lambda {e} {f} = m≤m {2} *-mono p
            open Data.Nat.≤-Reasoning

    ρ-C-≤-pred-n : (x : C) → ρ (C.e₂ x) f ≤ ρ e f → suc(ρ e f) ≤ ⌈ (pred (n)) /2⌉ → ⊥
    ρ-C-≤-pred-n x v u = e₂≢e (cong neck (A₂ (ρ-C-c₁ x v , ρ-C-c₁-len {x} {v} (fromWitness u)) (ρ-C-c₂ x , ρ-C-c₂-len {x} (fromWitness u))))
      where open C x
      
    ρ-C-ppc : (x : C) → ppchain e f
    ρ-C-ppc x = ((e ∶⟨ C.e₁ x ⟩∶ sppc (C.e₂ x) f)) {{fromWitness (#sym (toWitness (C.e#e₁ x)))}} {{fromWitness (#sym (toWitness (C.e₂#e₁ x)))}}

    ρ-C-ppc-≤n/2 : (x : C) → ρ (C.e₂ x) f < ρ e f  → (ρ' (ρ-C-ppc x) < ⌈ n /2⌉)
    ρ-C-ppc-≤n/2 x l = begin
                           suc (suc (ρ e₂ f)) ≤⟨ s≤s l ⟩
                           suc (ρ e f) ≤⟨ toWitness ≤n ⟩ (⌈ n /2⌉ ∎)
      where open C x
            open Data.Nat.≤-Reasoning
  
    -- The case when 2 * r = ( n - 1 ).
    -- We know that ρ e₂ f ≤ n/2 from Axiom 1
    ρ-C₁-pred-n₀ : (x : C) → 2 * (ρ e f) ≡ pred (n) → ρ (C.e₂ x) f < ρ e f → ⊥
    ρ-C₁-pred-n₀ x p q with A₂-ρ (ρ-C-ppc x , ρ-C-ppc-≤n/2 x q ) (sppc e f , toWitness ≤n)
    ... | z = C.e₁≢e₁⋆ x (helper z {≥1₁ = ≥1})
        where helper : {pc pc' : ppchain e f} → pc ≡ pc' → {≥1₀ : True (1 ≤? ρ' pc)} → {≥1₁ : True (1 ≤? ρ' pc')} → Subset.elem (neckl pc ≥1₀) ≡ Subset.elem (neckl pc' ≥1₁)
              helper refl = refl
