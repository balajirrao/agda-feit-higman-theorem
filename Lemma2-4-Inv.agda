open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import Relation.Binary.Core

open import Relation.Binary.PropositionalEquality as PropEq hiding (proof-irrelevance)

open import Data.Empty
open import Data.Unit hiding (_≤?_; _≤_; _≟_)

open import Data.Product 

open import Data.Bool hiding (_≟_)

open import Data.Nat hiding (compare) renaming (_≟_ to _ℕ≟_)
--open Data.Nat.≤-Reasoning

--open import Function.Inverse
open import Data.Sum

open import Data.Nat.Properties
open SemiringSolver

open import Function hiding (_∘_)
open import Function.Equality hiding (_∘_) renaming (cong to Icong)
open import Function.Inverse renaming (sym to Isym; zip to Izip; id to Iid)
open import Function.LeftInverse hiding (_∘_)

open import Function.Bijection hiding (_∘_)

import Data.Fin as F
import Data.Fin.Props as F

open import Function.Related.TypeIsomorphisms

import Relation.Binary.Sigma.Pointwise as SP

open import FinBijections

open import Data.Vec hiding ([_])

open import Misc

module Lemma2-4-Inv where
  
  open import Lemma2-4 public
 
  module 0<ρ<predn/2⁻¹ {e f : P} {≥1 : True (1 ≤? ρ e f)}
                       {<predn : True (suc (ρ e f) ≤? ⌈ (pred (n)) /2⌉)} where
    <n : True (suc (ρ e f) ≤? ⌈ n /2⌉)
    <n = fromWitness (begin
                     suc (ρ e f)
                       ≤⟨ toWitness <predn ⟩
                     ⌈ pred n /2⌉
                       ≤⟨ ⌈n/2⌉-mono (≤⇒pred≤ n n m≤m) ⟩
                     (⌈ n /2⌉ ∎))
      where open Data.Nat.≤-Reasoning

    class-B : (nck : Neck e) → ρ (neck-e₂ nck) f ≡ ρ e f → e ≢ (neck-e₂ nck) →
                     el (proj₁ nck) ≡ el (proj₁ (neck⋆ e f {≥1})) ×
                       (neck-e₂ nck) ≢ (neck-e₂ (neck⋆ e f {≥1}))
                        
    class-B  nck ρ≡ ≢e with pt (neck-e₂ nck) #? ln (el (proj₁ (neck⋆ e f {≥1})))
    class-B nck ρ≡ ≢e | yes p with pt (neck-e₂ nck) ≟ pt (neck-e₂ (neck⋆ e f {≥1}))
    class-B nck ρ≡ ≢e | yes p₁ | yes p = ⊥-elim (¬<-≡ (toWitness ≥1)
                                         (sym (≡pred⇒zero (trans (sym ρ≡)
                                           (0<ρ<n/2.class-A-ρ nck (pt-inj p))))))
    class-B nck ρ≡ ≢e | yes p | no ¬p = cong el (cong proj₁
                                             (neck!
                                             {nck = nck}
                                             {nck' = (proj₁ $ neck⋆ e f {≥1}) ,
                                               (neck-e₂ nck) ∶ ((#sym p))} ≢e refl)) ,
                                                 (λ x → ¬p (cong pt x))

    class-B nck ρ≡ ≢e | no ¬p = ⊥-elim
                                (≡suc⇒⊥ (trans
                                  (sym (0<ρ<n/2.class-C₀-ρ {e} {f} {≥1} {<n}
                                    nck (λ eq → ⊥-elim (¬p (helper
                                      ((#sym (neck-e₁#e₂ nck))) (cong ln eq))))
                                        (λ e₂≡e → ≢e (sym e₂≡e))
                                           (toWitness <predn))) ρ≡))
      where helper : ∀ {x y z} → x # y → y ≡ z → x # z
            helper # refl = #

  
    class-C : (nck : Neck e) → neck-e₂ nck ≢ e → ρ (neck-e₂ nck) f ≡ 1 + ρ e f →
                                             (neck-e₁ nck ≢ neck-e₁ (neck⋆ e f {≥1}))
    class-C nck ≢e ρ≡ e≡e₁⋆ with ln (neck-e₁ nck) ≟ ln (neck-e₁ (neck⋆ e f {≥1}))
    ... | no ¬p = ¬p (cong ln e≡e₁⋆)
    ... | yes p
            with (pt (neck-e₂ nck)) ≟ pt (neck-e₂ (neck⋆ e f {≥1}))
    ... | yes e≡e₂⋆ = helper (trans (sym ρ≡)
                                     (0<ρ<n/2.class-A-ρ nck (pt-inj e≡e₂⋆)))
      where helper : ∀ {x} → suc x ≡ pred x → ⊥
            helper {zero} ()
            helper {suc x} ()
    ... | no ¬p = ≡suc⇒⊥ (trans (sym ρ≡)
                   (0<ρ<n/2.class-B-ρ nck
                                      (ln-inj p)
                                      (λ x → ¬p (cong pt x)) ≢e))

  module ρ≡1/2-predn⁻¹ {e f : P}
         {ρ≡ : True (ρ e f ℕ≟ ⌈ (pred (n)) /2⌉)} {oddn : Odd n} where

    ≥1 : True (1 ≤? ρ e f )
    ≥1 = fromWitness (begin 1
                     ≤⟨ s≤s z≤n ⟩ ⌈ pred n /2⌉
                     ≡⟨ sym (toWitness ρ≡) ⟩ (ρ e f ∎))
      where open Data.Nat.≤-Reasoning

    <n : True (suc (ρ e f) ≤? ⌈ n /2⌉)
    <n = fromWitness (begin suc (ρ e f)
                     ≡⟨ cong suc (toWitness ρ≡) ⟩ suc ⌈ pred n /2⌉
                     ≡⟨ cong suc (helper oddn) ⟩ suc (pred ⌈ n /2⌉)
                     ≡⟨ refl ⟩ (⌈ n /2⌉ ∎))
      where open Data.Nat.≤-Reasoning
            helper : ∀ {x} → Odd x → ⌈ pred x /2⌉ ≡ pred ⌈ x /2⌉
            helper {zero} ox = refl
            helper {suc zero} ox = refl
            helper {suc (suc m)} (oddSuc ox) = sym (lem-even⇒⌊≡⌋ (oddEven ox))

    class-B : (nck : Neck e) → ρ (neck-e₂ nck) f ≡ ρ e f → e ≢ (neck-e₂ nck) →
                       (neck-e₂ nck) ≢ (neck-e₂ (neck⋆ e f {≥1}))
    class-B nck ρ≡ e≢ e₂≡e₂⋆ = (¬<-≡ (toWitness ≥1)
                                     (sym (≡pred⇒zero (trans (sym ρ≡)
                                          (0<ρ<n/2.class-A-ρ {≥1 = ≥1}
                                                             {<n = <n}
                                                               nck e₂≡e₂⋆)))))

  module ρ≡n/2⁻¹ {e f : P} {n-even : Even (n)}
                      {≡n/2 : True ( ρ e f  ℕ≟ ⌈ (n) /2⌉ )} where
     
    ≥1 : True (1 ≤? ρ e f )
    ≥1 = fromWitness (begin 1 ≤⟨ s≤s z≤n ⟩ ⌈ n /2⌉
                              ≡⟨ sym $ toWitness ≡n/2 ⟩
                     (ρ e f ∎))
      where open Data.Nat.≤-Reasoning

    class-A₀ : (nck : Neck e) →  ρ (neck-e₂ nck) f ≡ pred ⌈ (n) /2⌉ →
               (neck-e₂ nck) ≡ ρ≡n/2.e₂⋆ {n-even = n-even} {≡n/2 = ≡n/2} (proj₁ nck)
    class-A₀ nck ρ≡ with pt (neck-e₂ nck) ≟ pt (ρ≡n/2.e₂⋆ {n-even = n-even}
                                                          {≡n/2 = ≡n/2} (proj₁ nck))
    ... | yes p = pt-inj p
    ... | no ¬p = ⊥-elim (¬<-≡ (s≤s z≤n)
                 (sym $ (≡pred⇒zero $
                   trans (sym (ρ≡n/2.class-A₁-ρ
                     nck (λ x → ¬p (cong pt x)))) ρ≡)))

    class-A₁ :  (nck : Neck e) →  ρ (neck-e₂ nck) f ≡ ⌈ (n) /2⌉ →
                (neck-e₂ nck) ≢ ρ≡n/2.e₂⋆ {n-even = n-even} {≡n/2 = ≡n/2} (proj₁ nck)
    class-A₁ nck ρ≡ with pt (neck-e₂ nck) ≟ pt (ρ≡n/2.e₂⋆ {n-even = n-even}
                                                          {≡n/2 = ≡n/2} (proj₁ nck))
    ... | yes p = ⊥-elim (≡suc⇒⊥ (trans (sym ρ≡) (ρ≡n/2.class-A₀-ρ nck (pt-inj p))))
    ... | no ¬p = λ eq → ¬p (cong pt eq)
    
  module 0<ρ<n/2⁻¹ {e f : P} {≥1 : True (1 ≤? ρ e f)}
                   {<n : True (suc (ρ e f) ≤? ⌈ n /2⌉)} where

    class-A : (nck : Neck e) → ρ (neck-e₂ nck) f ≡ pred (ρ e f) →
              e ≢ (neck-e₂ nck) →(neck-e₂ nck) ≡ (neck-e₂ (neck⋆ e f {≥1}))

    class-A nck ρ≡ ≢e with pt (neck-e₂ nck) ≟ pt (neck-e₂ (neck⋆ e f {≥1})) |
                           ln (neck-e₁ nck) ≟ ln (neck-e₁ (neck⋆ e f {≥1}))
    ... | yes p | yes p₁ = pt-inj p
    ... | yes p | no ¬p = ⊥-elim (¬p
                                 (cong ln
                                   (cong neck-e₁
                                         (neck! {nck = nck}
                                                {nck' = (proj₁ $ neck⋆ e f {≥1}) ,
                                   neck-e₂ (neck⋆ e f {≥1}) ∶
                                     neck-e₁#e₂ (neck⋆ e f {≥1})} ≢e (pt-inj p)))))
    ... | no ¬p | yes p = ⊥-elim (¬<-≡ (toWitness ≥1)
                                       (sym (≡pred⇒zero
                                         (sym
                                           (trans (sym ρ≡)
                                             (0<ρ<n/2.class-B-ρ nck
                                                                (ln-inj p)
                                             (λ x → ¬p (cong pt x))
                                                       (λ x → ≢e (sym x))))))))
    ... | no ¬p | no ¬p₁ with parity n
    ... | isEven x = ⊥-elim (helper
                            (trans (sym
                              (0<ρ<n/2.class-C₀-ρ nck
                                (λ x₁ → ¬p₁ (cong ln x₁))
                                  (λ x₁ → ≢e (sym x₁)) helper₀)) ρ≡))
      where ρ<predn/2 : ∀ {x} → Even (suc (suc (suc x))) →
                              ⌈ (suc (suc x)) /2⌉ ≡ ⌈ (suc (suc (suc x))) /2⌉
            ρ<predn/2 {zero} (evenSuc ())
            ρ<predn/2 {suc zero} en = refl
            ρ<predn/2 {suc (suc x₁)} (evenSuc en) = cong suc (ρ<predn/2 en)

            helper₀ : ρ e f < ⌈ suc (suc nn) /2⌉
            helper₀ = begin suc (ρ e f) ≤⟨ toWitness <n ⟩ ⌈ n /2⌉
                                        ≡⟨ sym (ρ<predn/2 x) ⟩
                            (⌈ pred n /2⌉ ∎)
              where open Data.Nat.≤-Reasoning

            helper : ∀ {x} → suc x ≡ pred x → ⊥
            helper {zero} ()
            helper {suc x} ()
  
    ... | isOdd x with  suc (ρ e f) ≤? ⌈ (pred n) /2⌉
    ... | yes p = ⊥-elim
                  (helper
                    (trans
                      (sym
                        (0<ρ<n/2.class-C₀-ρ nck (λ x₁ → ¬p₁ (cong ln x₁))
                          (λ x₁ → ≢e (sym x₁)) p)) ρ≡))
      where helper : ∀ {x} → suc x ≡ pred x → ⊥
            helper {zero} ()
            helper {suc x} ()
    class-A nck ρ≡ ≢e | no ¬p₁ | no ¬p₂ | isOdd x | no ¬p =
                ⊥-elim (¬<-≡ (toWitness ≥1) (sym (≡pred⇒zero
                       (sym (trans (sym ρ≡)
                         (0<ρ<n/2.class-C₁-ρ nck (λ x₁ → ¬p₂ (cong ln x₁))
                           (λ x₁ → ¬p₁ (cong pt x₁))
                             (λ x₁ → ≢e (sym x₁)) ρ≡predn/2))))))
      where ρ≡predn/2 : (ρ e f) ≡ ⌈ (pred n) /2⌉
            ρ≡predn/2 = ≤-≥⇒≡ (begin ρ e f ≤⟨ pred-mono (toWitness <n) ⟩ pred ⌈ n /2⌉ 
                                           ≡⟨ sym (helper x) ⟩
                                             (⌈ pred n /2⌉ ∎)) (pred-mono (≰⇒> ¬p))
              where open Data.Nat.≤-Reasoning

                    helper : ∀ {x} → Odd x → ⌈ pred x /2⌉ ≡ pred ⌈ x /2⌉
                    helper {zero} ox = refl
                    helper {suc zero} ox = refl
                    helper {suc (suc m)} (oddSuc ox) = sym (lem-even⇒⌊≡⌋ (oddEven ox))
