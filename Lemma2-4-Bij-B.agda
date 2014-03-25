open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

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

open import Function.Equivalence hiding (_∘_)


import Data.Fin as F
import Data.Fin.Props as F

open import Function.Related.TypeIsomorphisms

import Relation.Binary.Sigma.Pointwise as SP

open import FinBijections

import Relation.Binary.HeterogeneousEquality as H

open import Data.Vec hiding ([_])

open import Misc

open import Lemma2-4-Inv

module Lemma2-4-Bij-B where
 

  postulate
    Σ↔ : 
        {A₁ A₂ : Set}
        {B₁ : A₁ → Set} {B₂ : A₂ → Set}
        (A₁↔A₂ : A₁ ↔ A₂) →
        (∀ {x} → B₁ x ⇔ B₂ (Inverse.to A₁↔A₂ ⟨$⟩ x)) →
        (Σ A₁ B₁) ↔ Σ A₂ B₂

  ln-val : ∀ {e} → L# e → F.Fin (1 + t) 
  ln-val {e} x = Inverse.to (GP-L e) ⟨$⟩ x

  ln-val⁻¹ : F.Fin (1 + t) → ∀ {e} → L# e
  ln-val⁻¹ y {e} = Inverse.from (GP-L e) ⟨$⟩ y

  ln-val-id₀ : ∀ {e x} → ln-val⁻¹ (ln-val {e} x) ≡ x
  ln-val-id₀ {e} {x} = Inverse.left-inverse-of (GP-L e) x

  pt-val : ∀ {e₁} → P# e₁ → F.Fin (1 + s)
  pt-val {e₁} x = Inverse.to (GP-P e₁) ⟨$⟩ x

  pt-val-inj : ∀ {e₁ x y} → pt-val {e₁} x ≡ pt-val y → x ≡ y
  pt-val-inj {e₁} eq = Inverse.injective (GP-P e₁) eq
  
  pt-val⁻¹ : F.Fin (1 + s) → ∀ {e₁} → P# e₁
  pt-val⁻¹ y {e₁} = Inverse.from (GP-P e₁) ⟨$⟩ y

  pt-val-on : ∀ {e} (x : F.Fin (1 + t)) → P# (el (ln-val⁻¹ x {e})) → F.Fin (1 + s)
  pt-val-on x y = pt-val y

  pt-val-on⁻¹ : F.Fin (1 + s) → ∀ {e} {x} → P# (el (ln-val⁻¹ x {e}))
  pt-val-on⁻¹ y = pt-val⁻¹ y

  pt-val-on-inj : ∀ {e} (x : F.Fin (1 + t)) → (a b : P# (el (ln-val⁻¹ x {e}))) → pt-val-on x a ≡ pt-val-on x b → a ≡ b
  pt-val-on-inj {e} x a b eq = Inverse.injective (GP-P (el (ln-val⁻¹ x {e}))) eq

  pt-val-on⁻¹-inj : {a b : F.Fin (1 + s)} → ∀ {e} {x} →  pt-val-on⁻¹ a {e} {x} ≡  pt-val-on⁻¹ b → a ≡ b
  pt-val-on⁻¹-inj {a} {b} {e} {x} eq = Inverse.injective (Isym (GP-P (el (ln-val⁻¹ x {e})))) eq
  
  pt-val-on-id₀ : ∀ {e x a} → pt-val-on⁻¹ (pt-val-on {e} x a) ≡ a
  pt-val-on-id₀ {e} {x} {a} = Inverse.left-inverse-of (GP-P (el (ln-val⁻¹ x {e}))) a

  pt-val-on-id₁ : ∀ {e x a} → pt-val-on x (pt-val-on⁻¹ a) ≡ a
  pt-val-on-id₁ {e} {x} {a} = Inverse.right-inverse-of (GP-P (el (ln-val⁻¹ x {e}))) a
                    
  module Bijection₅ (e f : P) (e₂⋆ : (e₁ : L# e) → P# (el e₁)) where
    bij : Σ (Neck e) (λ nck → (neck-e₂ nck) ≡ el (e₂⋆ (proj₁ nck))) ↔ F.Fin (1 + t)
    bij = record { to = record { _⟨$⟩_ = to ; cong = cong to } ; from = record { _⟨$⟩_ = from ; cong = cong from } ; inverse-of = record { left-inverse-of = left-inverse-of ; right-inverse-of = right-inverse-of } }
      where to : Σ (Neck e) (λ nck → (neck-e₂ nck) ≡ el (e₂⋆  (proj₁ nck))) → F.Fin (1 + t)
            to ((e₁ , ._ ∶ e₁#e₂) , refl) = ln-val e₁

            from : F.Fin (1 + t) → Σ (Neck e) (λ nck → (neck-e₂ nck) ≡ el (e₂⋆  (proj₁ nck)))
            from x = ((ln-val⁻¹ x) , e₂⋆ (ln-val⁻¹ x)) , refl

            left-inverse-of : ∀ x → from (to x) ≡ x
            left-inverse-of ((e₁ , ._ ∶ pf) , refl) rewrite (Inverse.left-inverse-of (GP-L e)) e₁  = refl

            right-inverse-of : ∀ x → to (from x) ≡ x
            right-inverse-of x = Inverse.right-inverse-of (GP-L e) x
  

  module Bijection₁  (e f : P) (nck⋆ : Neck e) where
    bij : Σ (Neck e) (λ nck → nck ≡ nck⋆) ↔ F.Fin 1
    bij = fin-one nck⋆ --record { to = record { _⟨$⟩_ = to ; cong = cong to } ; from = record { _⟨$⟩_ = from ; cong = cong from } ; inverse-of = record { left-inverse-of =  left-inverse-of ; right-inverse-of = right-inverse-of } }
      where to : Σ (Neck e) (λ nck → nck ≡ nck⋆) → F.Fin 1
            to _ = F.zero
                 
            from :  F.Fin 1 → Σ (Neck e) (λ nck → nck ≡ nck⋆)
            from F.zero = nck⋆ , refl
            from (F.suc ())

            left-inverse-of : ∀ x → from (to x) ≡ x
            left-inverse-of (el , pf) rewrite pf = refl

            right-inverse-of : ∀ x → to (from x) ≡ x
            right-inverse-of F.zero = refl
            right-inverse-of (F.suc ())

  module Bijection₂ (e f : P) (nck⋆ : Neck e) (distinct : (neck-e₂ nck⋆) ≢ e) where
      
    A : Neck e → Set
    A =  (λ nck → ((neck-e₁ nck) ≡ (neck-e₁ nck⋆) ×
                              (neck-e₂ nck) ≢ (neck-e₂ nck⋆)) ×
                                e ≢ (neck-e₂ nck))

    B : ∀ t₀ s₀ s₁ → (F.Fin (1 + t) × F.Fin (1 + s)) → Set
    B t₀ s₀ s₁ x = proj₁ x ≡ t₀ × proj₂ x ≢ s₀ × proj₂ x ≢ s₁

    S₀ = Σ (Neck e) A
    
    S₁ : ∀ t₀ s₀ s₁ → Set
    S₁ t₀ s₀ s₁ = Σ (F.Fin (1 + t) × F.Fin (1 + s)) (B t₀ s₀ s₁)
    
    S₂ = F.Fin (pred s)

    bij₀ : S₀ ↔ S₁ (ln-val (proj₁ nck⋆)) (pt-val (proj₂ nck⋆)) (pt-val (e ∶ (T#sym (neck-e#e₁ nck⋆))))
    bij₀ = Σ↔ neck-value-bij (λ {x} → record { to = record { _⟨$⟩_ = to {x} ; cong = cong to } ; from = record { _⟨$⟩_ = from {x} ; cong = cong (from {x}) } })
      where to : {x : Neck e} →
                 A x →
                 B (ln-val (proj₁ nck⋆)) (pt-val (proj₂ nck⋆)) (pt-val (e ∶ (T#sym (neck-e#e₁ nck⋆)))) (neck-value x)
            to {._ ∶ proof , e₂ ∶ proof′} ((refl , ≢₁) , ≢₂) = refl , ((λ x → ≢₁ (cong el $ pt-val-inj x)) , (λ x → ≢₂ (PropEq.sym $ cong el $ pt-val-inj x)))
            
            from :  {x : Neck e} →
                     B (ln-val (proj₁ nck⋆)) (pt-val (proj₂ nck⋆)) (pt-val (e ∶ (T#sym (neck-e#e₁ nck⋆)))) (neck-value x) →
                     A x
            from {e₁ ∶ e#e₁ , e₂ ∶ e₁#e₂} (a , b , c) with (Inverse.injective (GP-L e) a)
            from {._ ∶ e#e₁ , e₂ ∶ e₁#e₂} (a , b , c) | refl = (refl , (λ x → b (Icong (Inverse.to (GP-P (el (proj₁ nck⋆))))
                                                                                   (Σ'≡ {x = e₂ ∶ e₁#e₂} x)))) , (λ x → c (PropEq.sym (Icong (Inverse.to (GP-P (el (proj₁ nck⋆)))) (Σ'≡ {x = e ∶ _} {y = e₂ ∶ e₁#e₂} x))))
    
       
    bij₁ : ∀ t₀ s₀ s₁ → S₁ t₀ s₀ s₁ ↔ Σ (Σ (F.Fin (1 + t)) (λ x → x ≡ t₀)) (λ _ → Σ (F.Fin (1 + s)) (λ x → x ≢ s₀ × x ≢ s₁))
    bij₁ t₀ s₀ s₁ = record { to = record { _⟨$⟩_ = λ x → ((proj₁ $ proj₁ x) , (proj₁ $ proj₂ x)) , (proj₂ $ proj₁ x) , (proj₂ $ proj₂ x) ; cong = cong _ } ; from = record { _⟨$⟩_ = λ x → ((proj₁ $ proj₁ x) , (proj₁ $ proj₂ x)) , ((proj₂ $ proj₁ x) , (proj₂ $ proj₂ x)) ; cong = cong _ } ; inverse-of = record { left-inverse-of = λ x → refl ; right-inverse-of = λ x → refl } }

    bij₂ : ∀ t₀ s₀ s₁ → s₀ ≢ s₁ → (Σ (Σ (F.Fin (1 + t)) (λ x → x ≡ t₀)) (λ _ → Σ (F.Fin (1 + s)) (λ x → x ≢ s₀ × x ≢ s₁))) ↔ (Σ (F.Fin 1) (λ _ → F.Fin (pred s)))
    bij₂ t₀ s₀ s₁ neq = SP.↔ (fin-one t₀) (fin-exclude₂ {pred s} s₀ s₁ neq)

    bij₃ : F.Fin (pred s) ↔ (Σ (F.Fin 1) (λ _ → F.Fin (pred s)))
    bij₃ = record { to = record { _⟨$⟩_ = λ x → F.zero , x ; cong = cong _ } ; from = record { _⟨$⟩_ = λ x → proj₂ x ; cong = cong _ } ; inverse-of = record { left-inverse-of = λ x → refl ; right-inverse-of = λ x → helper x } }
      where helper : ∀ x → (F.zero {0} , proj₂ x) ≡ x
            helper (F.zero , proj₂) = refl
            helper (F.suc () , proj₂)

    bij : S₀ ↔ F.Fin (pred s)
    bij = Isym bij₃ ∘ bij₂ (ln-val (proj₁ nck⋆)) (pt-val (proj₂ nck⋆)) (pt-val (e ∶ T#sym (neck-e#e₁ nck⋆))) (λ eq → distinct (cong el $ pt-val-inj eq)) ∘ bij₁ _ _ _ ∘ bij₀

  module Bijection₃ (e f : P) (nck⋆ : Neck e) where
    
    S : Neck e → Set
    S = (λ nck → (proj₁ nck) ≢ (proj₁ nck⋆) × e ≢ (neck-e₂ nck))

    A = Σ (Neck e) S

    bij₁ : (Σ (Neck e) (λ nck → proj₁ nck ≢ proj₁ nck⋆ × e ≢ neck-e₂ nck)) ↔ (Σ (F.Fin (1 + t) × (F.Fin (1 + s))) (λ y → proj₁ y ≢ ln-val (proj₁ nck⋆) × proj₂ y ≢ pt-val-on (proj₁ y) (e ∶ T#sym (pf (ln-val⁻¹ (proj₁ y))))))
    bij₁ = Σ↔ neck-value-bij (λ {x} → (SP.⇔ (record { to = record { _⟨$⟩_ = to₀ x ; cong = cong (to₀ x) } ; from = record { _⟨$⟩_ = from₀ x ; cong = cong (from₀ x) } })
                             (to {x}) (from {x})))
      where to₀ : (x : Neck e) → proj₁ x ≢ proj₁ nck⋆ → ln-val (proj₁ x) ≢ ln-val (proj₁ nck⋆)
            to₀ x neq = λ eq → neq (Inverse.injective (GP-L e) eq)
            
            from₀ : (x : Neck e) → ln-val (proj₁ x) ≢ ln-val (proj₁ nck⋆) → proj₁ x ≢ proj₁ nck⋆
            from₀ x neq = λ eq → neq (cong ln-val eq)

            to : {x : Neck e} → e ≢ neck-e₂ x → proj₂ (neck-value x) ≢ pt-val-on (proj₁ (neck-value x)) (e ∶  T#sym (pf (ln-val⁻¹ (proj₁ (neck-value x)))))
            to {e₁ , e₂} neq with (ln-val-id₀ {e} {e₁})
            ... | a = λ eq → neq $
                                 cong el $
                                 PropEq.sym
                                 (pt-val-inj $
                                  subst
                                  (λ z →
                                     Inverse.to (GP-P (el e₁)) ⟨$⟩ e₂ ≡
                                     Inverse.to (GP-P (el z)) ⟨$⟩ e ∶ T#sym (pf z))
                                  a eq) 
            from : {x : Neck e} → proj₂ (neck-value x) ≢ pt-val-on (proj₁ (neck-value x)) (e ∶  T#sym (pf (ln-val⁻¹ (proj₁ (neck-value x))))) → e ≢ neck-e₂ x
            from {e₁ , e₂} neq = λ x₁ → neq (subst
                                                (λ z →
                                                   Inverse.to (GP-P (el e₁)) ⟨$⟩ e₂ ≡
                                                   Inverse.to (GP-P (el z)) ⟨$⟩ e ∶ T#sym (pf z))
                                                (PropEq.sym (ln-val-id₀ {e} {e₁}))
                                                (PropEq.sym (cong pt-val (Σ'≡ x₁))))
  
       
    bij₂ : ∀ t₀ → (g : (F.Fin (1 + t) → (F.Fin (1 + s)))) → (Σ (F.Fin (1 + t) × (F.Fin (1 + s))) (λ y → proj₁ y ≢ t₀ × proj₂ y ≢ (g (proj₁ y)))) ↔ Σ (Σ (F.Fin (1 + t)) (λ y → y ≢ t₀)) (λ x → (Σ (F.Fin (1 + s)) (λ y → y ≢ (g (proj₁ x)))))
    bij₂ t₀ g = record { to = record { _⟨$⟩_ = λ x → ((proj₁ (proj₁ x)) , (proj₁ (proj₂ x))) , (proj₂ (proj₁ x) , proj₂ (proj₂ x)) ; cong = cong _ } ;
                          from = record { _⟨$⟩_ = λ x → ((proj₁ $ proj₁ x) , (proj₁ $ proj₂ x)) , ((proj₂ $ proj₁ x) , (proj₂ $ proj₂ x)) ; cong = cong _ } ; inverse-of = record { left-inverse-of = λ x → refl ; right-inverse-of = λ x → refl } }

    bij₃ :  ∀ t₀ → (g : (F.Fin (1 + t) → (F.Fin (1 + s)))) →
              Σ (Σ (F.Fin (1 + t)) (λ y → y ≢ t₀)) (λ x → (Σ (F.Fin (1 + s)) (λ y → y ≢ (g (proj₁ x))))) ↔
              Σ (F.Fin t) (λ _ → F.Fin s)
    bij₃ t₀ g = SP.↔ (fin-exclude {t} t₀) (λ {x} → (fin-exclude {s} (g (proj₁ x))))

    bij : (Σ (Neck e) (λ nck → proj₁ nck ≢ proj₁ nck⋆ × e ≢ neck-e₂ nck)) ↔  (F.Fin (t * s))
    bij =  (prod-bij {t} {s}) ∘ (bij₃ _ _ ∘ (bij₂ _ _)) ∘ bij₁


  module Bijection₄ (e f : P) (nck⋆ : Neck e)  (distinct : (neck-e₂ nck⋆) ≢ e) where

    bij₀ : Σ (Neck e) (λ nck → nck ≢ nck⋆ × (neck-e₂ nck) ≢ e) ↔ Σ (Neck e) (λ nck → Bijection₂.A e f nck⋆ distinct nck ⊎ Bijection₃.S e f nck⋆ nck)
    bij₀ = Σ↔ Iid  (λ {x} → record { to = record { _⟨$⟩_ = to x ; cong = cong (to x) } ; from = record { _⟨$⟩_ = from x ; cong = cong (from x) } })
      where to : (x : Neck e) → (x ≢ nck⋆ × neck-e₂ x ≢ e) →
                    (Bijection₂.A e f nck⋆ distinct x ⊎
                    Bijection₃.S e f nck⋆ x)
            to nck proof with ln (neck-e₁ nck) ≟ ln (neck-e₁ nck⋆)
            to (._ ∶ e#e₁ , e₂)  proof | yes refl = inj₁ ((refl , (λ x → proj₁ proof (helper x))) , ≢sym (proj₂ proof))
              where helper : el e₂ ≡ (el $ proj₂ nck⋆) → (proj₁ nck⋆ , e₂) ≡ nck⋆
                    helper eq with e₂
                    helper refl | ._ ∶ _ = refl
            to nck proof | no ¬p =  inj₂ ((λ x → ¬p (cong ln (cong el x))) , (≢sym (proj₂ proof)))

            from : (x : Neck e) → (Bijection₂.A e f nck⋆ distinct x ⊎ Bijection₃.S e f nck⋆ x)
                   → (x ≢ nck⋆ × neck-e₂ x ≢ e)
            
            from (e₁ , e₂) (inj₁ x) = helper , (≢sym (proj₂ x))
              where helper : (e₁ , e₂) ≢ nck⋆
                    helper = λ x₁ → (proj₂ $ proj₁ x) (cong neck-e₂ x₁)
            from (e₁ , e₂) (inj₂ y) = helper , (≢sym (proj₂ y))
              where helper : (e₁ , e₂) ≢ nck⋆
                    helper = λ x₁ → proj₁ y (cong proj₁ x₁)

    bij₁ : Σ (Neck e) (λ nck → Bijection₂.A e f nck⋆ distinct nck ⊎ Bijection₃.S e f nck⋆ nck) ↔ (Bijection₂.S₀ e f nck⋆ distinct ⊎ Bijection₃.A e f nck⋆)
    bij₁ = record { to = record { _⟨$⟩_ = to ; cong = cong to } ; from = record { _⟨$⟩_ = from ; cong = cong from } ; inverse-of = record { left-inverse-of = left-inverse-of ; right-inverse-of = right-inverse-of } }
      where to : Σ (Neck e) (λ nck → Bijection₂.A e f nck⋆ distinct nck ⊎ Bijection₃.S e f nck⋆ nck) → (Bijection₂.S₀ e f nck⋆ distinct ⊎ Bijection₃.A e f nck⋆)
            to (nck , inj₁ x) = inj₁ (nck , x)
            to (nck , inj₂ y) = inj₂ (nck , y)

            from : (Bijection₂.S₀ e f nck⋆ distinct ⊎ Bijection₃.A e f nck⋆) →  Σ (Neck e) (λ nck → Bijection₂.A e f nck⋆ distinct nck ⊎ Bijection₃.S e f nck⋆ nck)
            from (inj₁ (nck , proof)) = nck , (inj₁ proof)
            from (inj₂ (nck , proof)) = nck , (inj₂ proof)
  
            left-inverse-of : ∀ x → from (to x) ≡ x
            left-inverse-of (nck , inj₁ x) = refl
            left-inverse-of (nck , inj₂ y) = refl

            right-inverse-of : ∀ x → to (from x) ≡ x
            right-inverse-of (inj₁ x) = refl
            right-inverse-of (inj₂ y) = refl

    bij₂ : (Bijection₂.S₀ e f nck⋆ distinct ⊎ Bijection₃.A e f nck⋆) ↔ (F.Fin (pred s) ⊎ F.Fin (t * s))
    bij₂ = Bijection₂.bij e f nck⋆ distinct ⊎-↔ Bijection₃.bij e f nck⋆
      where open import Relation.Binary.Sum

    bij : Σ (Neck e) (λ nck → nck ≢ nck⋆ × (neck-e₂ nck) ≢ e) ↔ (F.Fin (pred s + (t * s)))
    bij = sum-bij ∘ bij₂ ∘ bij₁ ∘ bij₀

module Bijection₆ (e f : P) (n-even : Even (n)) (≡n/2 : True ( ρ e f ℕ≟ ⌈ (n) /2⌉)) (e₂⋆ : (e₁ : L# e) → P# (el e₁))
                    (distinct : ∀ {l#e} → el (e₂⋆ l#e) ≢ e) where
    bij₁ : Σ (Neck e) (λ nck → (neck-e₂ nck) ≢ el (e₂⋆ (proj₁ nck)) × (neck-e₂ nck) ≢ e) ↔ Σ (F.Fin (1 + t) × F.Fin (1 + s)) (λ x → proj₂ x ≢ pt-val-on (proj₁ x) (e₂⋆ (ln-val⁻¹ (proj₁ x))) × proj₂ x ≢ pt-val-on (proj₁ x) (e ∶ (T#sym (pf (ln-val⁻¹ (proj₁ x))))))
    bij₁ = Σ↔ neck-value-bij (λ {x} → record { to = record { _⟨$⟩_ = to {x} ; cong = cong to } ; from = record { _⟨$⟩_ = from {x} ; cong = cong from } })
      where to : {x : Neck e} → (neck-e₂ x ≢ el (e₂⋆ (proj₁ x)) × neck-e₂ x ≢ e) →
                proj₂ (Inverse.to neck-value-bij ⟨$⟩ x) ≢
                  pt-val-on (proj₁ (Inverse.to neck-value-bij ⟨$⟩ x))
                  (e₂⋆ (ln-val⁻¹ (proj₁ (Inverse.to neck-value-bij ⟨$⟩ x))))
                  ×
                  proj₂ (Inverse.to neck-value-bij ⟨$⟩ x) ≢
                  pt-val-on (proj₁ (Inverse.to neck-value-bij ⟨$⟩ x)) (e ∶ (T#sym (pf (ln-val⁻¹ (ln-val (proj₁ x))))))
            to {x} neq = helper₁ , helper₂
               where helper₁ : proj₂ (Inverse.to neck-value-bij ⟨$⟩ x) ≢
                                     pt-val-on (proj₁ (Inverse.to neck-value-bij ⟨$⟩ x))
                                     (e₂⋆ (ln-val⁻¹ (proj₁ (Inverse.to neck-value-bij ⟨$⟩ x))))
                     helper₁ rewrite Inverse.left-inverse-of (GP-L e) (proj₁ x) = λ eq → proj₁ neq (cong el $ Inverse.injective (GP-P (el (proj₁ x))) eq)

                     helper₂ : proj₂ (Inverse.to neck-value-bij ⟨$⟩ x) ≢
                               pt-val-on (proj₁ (Inverse.to neck-value-bij ⟨$⟩ x)) (e ∶ _)
                     helper₂ = λ eq → proj₂ neq (cong el $ Inverse.injective (GP-P (el (proj₁ x))) (helper eq))
                       where helper : ∀ eq → Inverse.to (GP-P (el (proj₁ x))) ⟨$⟩ proj₂ x ≡ Inverse.to (GP-P (el (proj₁ x))) ⟨$⟩ (e ∶ _)
                             helper eq = subst (λ z → Inverse.to (GP-P (el (proj₁ x))) ⟨$⟩ proj₂ x ≡ Inverse.to (GP-P (el z)) ⟨$⟩ e ∶ (T#sym $ pf z)) (Inverse.left-inverse-of (GP-L e) (proj₁ x)) eq

            from : {x : Neck e} → proj₂ (Inverse.to neck-value-bij ⟨$⟩ x) ≢
                  pt-val-on (proj₁ (Inverse.to neck-value-bij ⟨$⟩ x))
                  (e₂⋆ (ln-val⁻¹ (proj₁ (Inverse.to neck-value-bij ⟨$⟩ x))))
                  ×
                  proj₂ (Inverse.to neck-value-bij ⟨$⟩ x) ≢
                  pt-val-on (proj₁ (Inverse.to neck-value-bij ⟨$⟩ x)) (e ∶ (T#sym (pf (ln-val⁻¹ (ln-val (proj₁ x)))))) →
                  (neck-e₂ x ≢ el (e₂⋆ (proj₁ x)) × neck-e₂ x ≢ e)
            from {x} (neq₁ , neq₂) = (λ eq → neq₁ (helper₁ eq)) , (λ eq → neq₂ (helper₂ eq))
              where helper₁ : neck-e₂ x ≡ el (e₂⋆ (proj₁ x)) →
                                      proj₂ (Inverse.to neck-value-bij ⟨$⟩ x) ≡
                                      pt-val-on (proj₁ (Inverse.to neck-value-bij ⟨$⟩ x))
                                      (e₂⋆ (ln-val⁻¹ (proj₁ (Inverse.to neck-value-bij ⟨$⟩ x))))
                    helper₁ eq rewrite eq | Inverse.left-inverse-of (GP-L e) (proj₁ x) = Icong (Inverse.to (GP-P (el (proj₁ x)))) (Σ'≡ eq)

                    helper₂ : neck-e₂ x ≡ e → proj₂ (Inverse.to neck-value-bij ⟨$⟩ x) ≡
                                              pt-val-on (proj₁ (Inverse.to neck-value-bij ⟨$⟩ x)) (e ∶ _)
                    helper₂ eq = subst (λ z → Inverse.to (GP-P (el (proj₁ x))) ⟨$⟩ proj₂ x ≡ Inverse.to (GP-P (el z)) ⟨$⟩ e ∶ (T#sym $ pf z)) (PropEq.sym $ Inverse.left-inverse-of (GP-L e) (proj₁ x)) (Icong (Inverse.to (GP-P (el (proj₁ x)))) (Σ'≡ eq))

    bij₂ : (g₀ g₁ : F.Fin (1 + t) → F.Fin (1 + s)) → Σ (F.Fin (1 + t) × F.Fin (1 + s)) (λ x → proj₂ x ≢ g₀ (proj₁ x) × proj₂ x ≢ g₁ (proj₁ x)) ↔ Σ (F.Fin (1 + t))  (λ x → Σ (F.Fin (1 + s)) (λ y → y ≢ g₀ x × y ≢ g₁ x))
    bij₂ g₀ g₁ = record { to = record { _⟨$⟩_ = λ x → (proj₁ $ proj₁ x) , ((proj₂ $ proj₁ x) , proj₂ x) ; cong = cong _ } ; from = record { _⟨$⟩_ = λ x → ((proj₁ x) , (proj₁ $ proj₂ x)) , (proj₂ $ proj₂ x) ; cong = cong _ } ; inverse-of = record { left-inverse-of = λ x → refl ; right-inverse-of = λ x → refl } }
    
    bij₃ : (g₀ g₁ : F.Fin (1 + t) → F.Fin (1 + s)) → (∀ z → g₀ z ≢ g₁ z) → Σ (F.Fin (1 + t))  (λ x → Σ (F.Fin (1 + s)) (λ y → y ≢ g₀ x × y ≢ g₁ x)) ↔ Σ (F.Fin (1 + t)) (λ _ → F.Fin (pred s))
    bij₃ g₀ g₁ neq = SP.↔ Iid (λ {x} → (fin-exclude₂ (g₀ x) (g₁ x) (neq x)))

    bij₄ : Σ (Neck e) (λ nck → (neck-e₂ nck) ≢ el (e₂⋆ (proj₁ nck)) × (neck-e₂ nck) ≢ e) ↔ Σ (F.Fin (1 + t)) (λ _ → F.Fin (pred s))
    bij₄  = bij₃ _ _ (λ z x → distinct {ln-val⁻¹ z} (cong el $ Inverse.injective (GP-P (el (ln-val⁻¹ z))) x)) ∘ bij₂ _ _ ∘ bij₁

    bij : Σ (Neck e) (λ nck → (neck-e₂ nck) ≢ el (e₂⋆ (proj₁ nck)) × (neck-e₂ nck) ≢ e) ↔ F.Fin ((1 + t) * (pred s))
    bij = prod-bij ∘ bij₄

module Bijection₀ (e f : P) where
    bij₁ : (g : (F.Fin (1 + t) → (F.Fin (1 + s)))) →
              Σ (F.Fin (1 + t)) (λ x → (Σ (F.Fin (1 + s)) (λ y → y ≢ (g x)))) ↔
              Σ (F.Fin (1 + t)) (λ _ → F.Fin s)
    bij₁ g = SP.↔ Iid (λ {x} → fin-exclude {s} (g x))

    bij₂ : (g : (F.Fin (1 + t) → (F.Fin (1 + s)))) → (Σ (F.Fin (1 + t) × (F.Fin (1 + s))) (λ y → proj₂ y ≢ (g (proj₁ y)))) ↔ Σ (F.Fin (1 + t)) (λ x → (Σ (F.Fin (1 + s)) (λ y → y ≢ (g x))))
    bij₂ g = record { to = record { _⟨$⟩_ = λ x → (proj₁ $ proj₁ x) , ((proj₂ $ proj₁ x) , proj₂ x) ; cong = cong _ } ;
                          from = record { _⟨$⟩_ = λ x → ((proj₁ x) , (proj₁ $ proj₂ x)) , (proj₂ $ proj₂ x) ; cong = cong _ } ; inverse-of = record { left-inverse-of = λ x → refl ; right-inverse-of = λ x → refl } }

    bij₃ : Σ (Neck e) (λ nck → (neck-e₂ nck) ≢ e) ↔  Σ (F.Fin (1 + t) × F.Fin (1 + s)) (λ y → proj₂ y ≢ pt-val-on (proj₁ y) (e ∶ T#sym (pf (ln-val⁻¹ (proj₁ y)))))
    bij₃ = Σ↔ neck-value-bij (λ {x} → record
                                        { to = record { _⟨$⟩_ = to {x} ; cong = cong to }
                                        ; from = record { _⟨$⟩_ = from {x} ; cong = cong from }
                                        })

      where to : {x : Neck e} → neck-e₂ x ≢ e → proj₂ (neck-value x) ≢ pt-val-on (proj₁ (neck-value x)) (e ∶  T#sym (pf (ln-val⁻¹ (proj₁ (neck-value x)))))
            to {e₁ , e₂} neq with (ln-val-id₀ {e} {e₁})
            ... | a = λ eq → (≢sym neq) $
                           cong el $
                           PropEq.sym
                           (pt-val-inj $
                            subst
                            (λ z →
                               Inverse.to (GP-P (el e₁)) ⟨$⟩ e₂ ≡
                               Inverse.to (GP-P (el z)) ⟨$⟩ e ∶ T#sym (pf z))
                            a eq) 
            from : {x : Neck e} → proj₂ (neck-value x) ≢ pt-val-on (proj₁ (neck-value x)) (e ∶  T#sym (pf (ln-val⁻¹ (proj₁ (neck-value x))))) → neck-e₂ x ≢ e
            from {e₁ , e₂} neq = λ x₁ → neq (subst
                                          (λ z →
                                             Inverse.to (GP-P (el e₁)) ⟨$⟩ e₂ ≡
                                             Inverse.to (GP-P (el z)) ⟨$⟩ e ∶ T#sym (pf z))
                                          (PropEq.sym (ln-val-id₀ {e} {e₁}))
                                          (PropEq.sym (cong pt-val (Σ'≡ (PropEq.sym x₁)))))    

    bij : Σ (Neck e) (λ nck → (neck-e₂ nck) ≢ e) ↔ F.Fin ((1 + t) * s)
    bij = ((prod-bij ∘ bij₁ _) ∘ bij₂ _) ∘ bij₃
      
