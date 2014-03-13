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

import Data.Fin as F
import Data.Fin.Props as F

open import Function.Related.TypeIsomorphisms

import Relation.Binary.Sigma.Pointwise as SP


open import FinBijections

open import Data.Vec hiding ([_])

open import Misc

module Lemma2-4-A where
  
  open import Lemma2-4
 
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
  
  M : (e f : P) (q : ℕ) → Set
  M e f q = Σ (ppchain e f) (λ ppc → ρ' ppc ≡ q)

  K : (e f : P) (i : (F.Fin ⌈ n /2⌉)) → Set
  K e f i = Σ (L# e) (λ e₁ → Σ' (P# (el e₁)) (λ e₂ → ρ (el e₂) f ≡ F.toℕ i))


--True (pt e #? ln e₁) × True (ln e₁ #? pt e₂) × ρ e₂ f ≡ Fin.toℕ i
  --postulate
  k : (r i : (F.Fin ⌈ n /2⌉)) → Σ ℕ (λ x → ∀ (e f : P) (eq : (ρ e f) ≡ (F.toℕ r)) → Inverse (F.setoid x) (PropEq.setoid (K e f i)))
  k r i with r F.≟ F.zero
  k .F.zero i | yes refl with i F.≟ F.suc F.zero
  k .F.zero .(F.suc F.zero) | yes refl | yes refl = {!!} --(1 + t) * s , (λ e f ρz → ((bij₄ e f ρz) ∘ (Isym $ bij₂ e) ∘ (Isym $ bij₃ e)) ∘ (Isym bij))
  k .F.zero i | yes refl | no ¬p = {!!}

  k r i | no ¬p = {!!}


{-
    where bij : Inverse (PropEq.setoid (F.Fin (1 + t) × F.Fin s)) (F.setoid ((1 + t) * s))
          bij = prod-bij

          bij₀ : (e f : P) (ρz : ρ e f ≡ 0) →  {e₁ : L# e} →
                 Inverse (PropEq.setoid (Σ' (P# (el e₁)) (λ z → el z ≢ e)))
                         (PropEq.setoid (Σ' (P# (el e₁)) (λ e₂ → ρ (el e₂) f ≡ 1)))

          bij₀ e f ρz {e₁} = (record { to = record { _⟨$⟩_ = to ; cong = cong to } ;
                                       from = record { _⟨$⟩_ = from ; cong = cong from } ;
                                       inverse-of = record {
                                                    left-inverse-of = λ _ → Σ'≡ refl ;
                                                    right-inverse-of = λ _ → Σ'≡ refl } })

               where to : Σ' (P# (el e₁)) (λ z → el z ≢ e) → Σ' (P# (el e₁)) (λ e₂ → ρ (el e₂) f ≡ 1)
                     to (e₂ ∶ neq) = e₂ ∶ ρe₂f≡1
                       where  .x≤1⇒x≡0or1 : ∀ {x} → x ≤ 1 → (x ≡ 0) ⊎ (x ≡ 1)
                              x≤1⇒x≡0or1 z≤n = inj₁ refl
                              x≤1⇒x≡0or1 (s≤s z≤n) = inj₂ refl
  
                              .ρe₂e≤1 : ρ (el e₂) e ≤ 1
                              ρe₂e≤1 = sppc-ρ-shorter-than ((el e₂) ∶⟨ (el e₁) ⟩∶ [ e ]) {{T#sym (pf e₂)}} {{T#sym (pf e₁)}}

                              .ρe₂e≡1 : ρ (el e₂) e ≡ 1
                              ρe₂e≡1 with x≤1⇒x≡0or1 (ρe₂e≤1)
                              ρe₂e≡1 | inj₁ x≡0 = ⊥-elim (neq (ρ≡0⇒e≡f x≡0))
                              ρe₂e≡1 | inj₂ x≡1 = x≡1
  
                              .ρe₂f≡ρe₂e : ρ (el e₂) f ≡ ρ (el e₂) e 
                              ρe₂f≡ρe₂e = cong (λ x₁ → ρ (el e₂) x₁) (sym (ρ≡0⇒e≡f ρz))

                              .ρe₂f≡1 : ρ (el e₂) f ≡ 1
                              ρe₂f≡1 = trans ρe₂f≡ρe₂e ρe₂e≡1

                     from : Σ' (P# (el e₁)) (λ e₂ → ρ (el e₂) f ≡ 1) → Σ' (P# (el e₁)) (λ z → el z ≢ e)
                     from (e₂ ∶ neq) = e₂ ∶ (λ eq → ρef≡1⇒⊥ (e≢e₂⇒ρef≡1 eq))
                       where  .e≢e₂⇒ρef≡1 : el e₂ ≡ e → ρ e f ≡ 1
                              e≢e₂⇒ρef≡1 eq = subst (λ x → ρ x f ≡ 1) (eq) neq
            
                              .ρef≡1⇒⊥ : ρ e f ≡ 1 → ⊥
                              ρef≡1⇒⊥ eq with trans (sym eq) ρz
                              ρef≡1⇒⊥ eq | ()
                       
          
          bij₄ :  (e f : P) (ρz : ρ e f ≡ 0) → Inverse
                  (PropEq.setoid (Σ (L# e) (λ e₁ → Σ' (P# (el e₁)) (λ z → el z ≢ e))))
                  (PropEq.setoid (K e f (F.suc F.zero)))
          bij₄ e f ρz = SP.↔ Iid (λ {e₁} → bij₀ e f ρz {e₁})

          bij₁ : (e : P) → ∀ {e₁ : L# e} → Inverse (PropEq.setoid (Σ' (P# (el e₁)) (λ z → el z ≢ e)))
                                                   (PropEq.setoid (Σ' (F.Fin (1 + s)) (λ y → y ≢ (pt-val (e ∶ (T#sym $ pf (ln-val⁻¹ (ln-val e₁))))))))

          bij₁ e {e₁} = record { to = record { _⟨$⟩_ = to ; cong = cong to } ;
                                 from = record { _⟨$⟩_ = from ; cong = cong from } ;
                                 inverse-of = record { left-inverse-of = left-inverse-of ; right-inverse-of = right-inverse-of } }

            where to : Σ' (P# (el e₁)) (λ z → el z ≢ e) → Σ' (F.Fin (1 + s)) (λ y → y ≢ (pt-val (e ∶ (T#sym $ pf (ln-val⁻¹ (ln-val e₁))))))
                  to (e₂ ∶ #) = (pt-val e₂) ∶ (λ eq → # (cong el $ helper eq))
                    where helper : pt-val e₂ ≡ pt-val (e ∶ (T#sym $ pf (ln-val⁻¹ (ln-val e₁)))) → _
                          helper eq = pt-val-inj $
                                        subst (λ z → pt-val e₂ ≡ pt-val (e ∶ (T#sym $ pf z)))
                                        (Inverse.left-inverse-of (GP-L e) e₁) eq

                  from : Σ' (F.Fin (1 + s)) (λ y → y ≢ (pt-val (e ∶ (T#sym $ pf (ln-val⁻¹ (ln-val e₁)))))) →  Σ' (P# (el e₁)) (λ z → el z ≢ e)
                  from (y ∶ neq) = (pt-val⁻¹ y) ∶ (λ eq → neq (helper (trans (sym (Inverse.right-inverse-of (GP-P (el e₁)) y)) (cong pt-val (Σ'≡ eq)))))

                    where helper : y ≡ pt-val (e ∶ (T#sym $ pf e₁)) → y ≡ (pt-val (e ∶ (T#sym $ pf (ln-val⁻¹ (ln-val e₁)))))
                          helper eq = subst (λ x → y ≡ pt-val (e ∶ (T#sym $ pf x))) (sym (Inverse.left-inverse-of (GP-L e) e₁)) eq

                  left-inverse-of : ∀ x → from (to x) ≡ x
                  left-inverse-of x = Σ'≡ (Inverse.left-inverse-of (GP-P (el e₁)) (el x))

                  right-inverse-of : ∀ x → to (from x) ≡ x
                  right-inverse-of x = Σ'≡ (Inverse.right-inverse-of (GP-P (el e₁)) (el x))
         
          bij₂ : (e : P) → Inverse (PropEq.setoid (Σ (L# e) (λ e₁ → Σ' (P# (el e₁)) (λ z → el z ≢ e))))
                                                     (PropEq.setoid (Σ (F.Fin (1 + t)) (λ x →  Σ' (F.Fin (1 + s)) (λ y → y ≢ (pt-val (e ∶ (T#sym $ pf (ln-val⁻¹ x))))))))

          bij₂ e = SP.↔ (GP-L e) (bij₁ e)

          bij₃ : (e : P) → Inverse (PropEq.setoid (Σ (F.Fin (1 + t)) (λ x →  Σ' (F.Fin (1 + s)) (λ y → y ≢ (pt-val (e ∶ (T#sym $ pf (ln-val⁻¹ x))))))))
                          (PropEq.setoid (F.Fin (1 + t) × F.Fin s))
          bij₃ e =  SP.↔ Iid (λ {x} → fin-exclude {s} (pt-val (e ∶ (T#sym $ pf (ln-val⁻¹ x)))))

  
  m : (r : F.Fin ⌈ n /2⌉) → (q : ℕ) → Σ ℕ (λ x → ∀ {e} {f} → Inverse  (Fin.setoid x) (PropEq.setoid (M e f q)))

  m r zero = {!!}

  m r (suc q) = ((1 + t) * proj₁ (m r q) + sum (tabulate (λ x → proj₁ (k r x) * proj₁ (m r q)))) ,
                record { to = record { _⟨$⟩_ = λ x → (λ {e} {f} → {!!}) {!!} ; cong = {!!} } ;
                         from = {!!} ;
                         inverse-of = {!!} }

    where
      F : ∀ {e f} → F.Fin (1 + t) × F.Fin (proj₁ (m r q)) ⊎ Σ (F.Fin ⌈ n /2⌉) (λ x → F.Fin (proj₁ (k r x)) × F.Fin (proj₁ (m x q))) → M e f (1 + q)
      F {e} {f} (inj₁ (e₁-v , c')) = c , ρ'c≡2q
        where e₁ = el (Inverse.from (GP-L e) ⟨$⟩ e₁-v)
                   
              .e#e₁ : True ((pt e) #? (ln e₁))
              e#e₁ = pf (Inverse.from (GP-L e) ⟨$⟩ e₁-v)

              c : ppchain e f
              c = _∶⟨_⟩∶_ e e₁ (proj₁ (Inverse.to (proj₂ (m r q)) ⟨$⟩ c')) {{e#e₁}} {{T#sym e#e₁}}
           
              ρ'c≡2q : ρ' c ≡ (suc q)
              ρ'c≡2q = cong suc (proj₂ (Inverse.to (proj₂ (m r q)) ⟨$⟩ c'))

      F {e} {f} (inj₂ (i , kᵢ , mᵢ)) = c , ρ'c≡2q
        where e₁ : L
              e₁ = neck-e₁ $ proj₁ $ (Inverse.to (proj₂ (k r i)) ⟨$⟩ kᵢ) {e} {f}
                   
              .e#e₁ : True ((pt e) #? (ln e₁))
              e#e₁ = neck-e#e₁ $ proj₁ $ Inverse.to (proj₂ (k r i)) ⟨$⟩ kᵢ

              e₂ : P
              e₂ = neck-e₂ $ proj₁ $ Inverse.to (proj₂ (k r i)) ⟨$⟩ kᵢ

              .e₁#e₂ :  True ((ln e₁) #? (pt e₂))
              e₁#e₂ = neck-e₁#e₂ $ proj₁ $ Inverse.to (proj₂ (k r i)) ⟨$⟩ kᵢ
  
              c : ppchain e f
              c = _∶⟨_⟩∶_ e e₁ (proj₁ (Inverse.to (proj₂ (m i q)) ⟨$⟩ mᵢ))
           
              ρ'c≡2q : ρ' c ≡ (suc q)
              ρ'c≡2q = cong suc (proj₂ (Inverse.to (proj₂ (m i q)) ⟨$⟩ mᵢ))




-}
