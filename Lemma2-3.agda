open import Data.Nat
open import Data.Nat.Properties

open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import Data.Fin using (Fin; toℕ; zero; suc)
open import Data.Fin.Properties

open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Product

open import Relation.Binary.PropositionalEquality as PropEq
--open PropEq.≡-Reasoning 

open import Relation.Nullary.Core

open import Function.Equality hiding (setoid; cong; _∘_)
open import Function.Inverse renaming (sym to Isym)

open import Misc

open import GenPolygon

open SemiringSolver


module Lemma2-3 where

  open import Lemma2-2
  open import Lemma2-4-core
  open import Lemma2-4

  lem-neck : ∀ {e f} → (c : chain e f) → Σ' ⊤ (λ _ → e # neck c)
  lem-neck [ e ] = tt ∶ #refl
  lem-neck (_∷_ e {{e<>f}} {{e#f}} c) = tt ∶ e#f

  lem-neck₁ :  ∀ {e f} → (c : chain e f) → (len c ≥ 1) → Σ' ⊤ (λ _ → e ≢ neck c)
  lem-neck₁ [ e ] ()
  lem-neck₁ (_∷_ e {{e<>f}} {{e#f}} c) leq = tt ∶ (λ x → e<>f x)

  F : ∀ {e f k} → (ρ e f ≡ k) →
                  ∃ (λ (x : P) → ρ x f ≡ (pred k))
  F {e} {f} {k = zero} eq = e , eq
  F {e} {f} {k = suc k} eq = neck-e₂ (neck⋆ e f {fromWitness helper}) ,
                                     trans (sym (trans (trans
                                       (cong pred sppc-is-ρ-shortest)
                             (sym (lem-tailpp-ρ {ppc = sppc e f})))
                               (tailpp-ρ-shortest sppc-is-ρ-shortest)))
                                                  (cong pred eq)
    where helper : 1 ≤ ρ e f
          helper rewrite eq = s≤s z≤n

  ppGP : (e : P) → ∃ (λ (f : P) → ρ e f ≡ ⌊ n /2⌋)
  ppGP e with (GP (pt e))
  ppGP e | pt x , p = x , trans (sym lem-lambda/2-ρ) (cong ⌊_/2⌋ p)
  ppGP e | ln x , proj₂ with neck ((sc (ln x) (pt e))) |
                             inspect neck ((sc (ln x) (pt e))) 
  ppGP e | ln x , p | pt x₁ | [ eq ] = x₁ ,
           trans (sym lem-lambda/2-ρ)
             (trans (cong ⌊_/2⌋
               (λfe≡λef {pt e} {pt x₁}))
                 (trans (cong ⌊_/2⌋
                   (subst (λ z →
                     lambda z (pt e) ≡
                       len (tail (sc (ln x) (pt e)))) eq
                           (sym (tail-shortest
                             {c = sc (ln x) (pt e)} sc-shortest))))
                   (trans (cong ⌊_/2⌋
                     (lem-tail-len {c = sc (ln x) (pt e)})) (trans
                       (cong ⌊_/2⌋
                         (cong pred (trans (sym (λfe≡λef {pt e} {ln x})) p)))
                           (cong pred (helper (subst Odd p
                                      (lem-pl {c = sc (pt e) (ln x)}))))))))
       where helper : ∀ {m} → Odd m → ⌊ (suc m) /2⌋ ≡ suc ⌊ m /2⌋
             helper oddOne = refl
             helper (oddSuc om) = cong suc (helper om)
  ppGP e | ln x , p | ln x₁ | [ eq ] rewrite λfe≡λef {pt e} {ln x} = ⊥-elim
                                     (IP-pt (subst (λ w → ln x ≢ w) eq
                                       (pf (lem-neck₁ (sc (ln x) (pt e))
                                     (subst (λ z → z ≥ 1) (sym p) (s≤s z≤n)))))
                                       (subst (λ w → ln x # w) eq
                                         (pf (lem-neck (sc (ln x) (pt e))))))
       where helper : len (sc (ln x) (pt e)) ≥ 1
             helper rewrite p = s≤s z≤n
  lem₁ : ∀ {x y} → x ∸ (suc y) ≡ pred (x ∸ y)
  lem₁ {zero} {zero} = refl
  lem₁ {zero} {suc y} = refl
  lem₁ {suc x} {zero} = refl
  lem₁ {suc x} {suc y} = lem₁ {x} {y}
  
  lem₂ : ∀ {e f k} → (l : ℕ) → ρ e f ≡ k → ∃ (λ (x : P) → ρ x f ≡ k ∸ l)
  lem₂ {e} zero eq = e , eq
  lem₂ {k = k} (suc l) eq rewrite lem₁ {k} {l} = F (proj₂ (lem₂ l eq))

  lem₃ : ∀ {a b} → b ≤ a → suc a ∸ b ≡ suc (a ∸ b)
  lem₃ z≤n = refl
  lem₃ (s≤s leq) = lem₃ leq

  lem₄ : ∀ {a b} → a ≤ b → ∃ (λ (c : ℕ) → a ≡ b ∸ c × c ≤ b)
  lem₄ {zero} {zero} z≤n = 0 , refl , z≤n
  lem₄ {zero} {suc b} leq = (suc b) , sym (n∸n≡0 b) , m≤m
  lem₄ {suc a} {zero} ()
  lem₄ {suc a} {suc b} (s≤s leq) = (proj₁ (lem₄ leq)) ,
                            (sym (trans (lem₃ {b} {proj₁ (lem₄ leq)}
                                 (proj₂ (proj₂ (lem₄ leq))))
                            (cong suc (sym (proj₁ (proj₂ (lem₄ leq)))))),
                                  ≤-steps 1 (proj₂ (proj₂ (lem₄ leq))))
  
  ρ-sym : ∀ {e f} → ρ e f ≡ ρ f e
  ρ-sym = trans (sym lem-lambda/2-ρ) (trans (cong ⌊_/2⌋ λfe≡λef) lem-lambda/2-ρ)
  
  lemma2-3 : ∀ {f k} → k ≤ ⌊ n /2⌋ →  ∃ (λ (x : P) → ρ x f ≡ k)
  lemma2-3 {f} {k} leq = proj₁ (lem₂ {proj₁ (ppGP f)} {f} {⌊ n /2⌋}
                               (proj₁ (lem₄ {k} {⌊ n /2⌋} leq))
                                 (trans ρ-sym (proj₂ (ppGP f)))) ,
                                        trans (proj₂ (lem₂ (proj₁ (lem₄ leq))
                               (trans ρ-sym (proj₂ (ppGP f)))))
                         (sym (proj₁ (proj₂ (lem₄ {k} {⌊ n /2⌋} leq))))
