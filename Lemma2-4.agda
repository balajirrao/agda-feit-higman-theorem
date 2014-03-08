open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import Relation.Binary.PropositionalEquality as PropEq hiding (proof-irrelevance)

open import Data.Bool hiding (_≟_) 
open import Data.Bool.Properties

open import Data.Empty
open import Data.Unit hiding (_≤?_; _≤_; _≟_)

open import Data.Product 

open import Data.Nat renaming (_≟_ to _ℕ≟_)
--open Data.Nat.≤-Reasoning

open import Data.Nat.Properties
open SemiringSolver

open import Function hiding (_∘_)
open import Function.Equality hiding (cong;  _∘_)
open import Function.Inverse hiding (sym)
open import Function.LeftInverse hiding (_∘_)

open import Misc
open import FinBijections

import Data.Fin as Fin
import Data.Fin.Properties as Fin

module Lemma2-4 where
  open import Lemma2-4-core public
 
  
  neck⋆ : ∀ (e f : P) → {≥1 : True (1 ≤? ρ e f)} → Neck e
  neck⋆ e f = ppneck (sppc e f)

  neck-value-f : ∀ {e} → Neck e → Fin.Fin (1 + t) × Fin.Fin (1 + s)
  neck-value-f {e} (x , y) = (Inverse.to (GP-L e) ⟨$⟩ x) , (Inverse.to (GP-P (Subset.elem x)) ⟨$⟩ y)

  neck-value-f⁻¹ : ∀ {e} → Fin.Fin (1 + t) × Fin.Fin (1 + s) → Neck e
  neck-value-f⁻¹ {e} ( x , y ) = e₁ , e₂
    where e₁ = Inverse.from (GP-L e) ⟨$⟩ x
          e₂ = Inverse.from (GP-P (Subset.elem e₁)) ⟨$⟩ y

  neck-value-id₀ : ∀ {e} (x : Neck e) →  neck-value-f⁻¹ (  neck-value-f x) ≡ x
  neck-value-id₀ {e} ((e₁ , e#e₁) , (e₂ , e₁#e₂)) with neck-value-f ((e₁ , e#e₁) , (e₂ , e₁#e₂))
  ... | z rewrite Inverse.left-inverse-of (GP-L e) (e₁ , e#e₁) | Inverse.left-inverse-of (GP-P e₁) (e₂ , e₁#e₂) = refl

  neck-value-id₁ : ∀ {e} (x :  Fin.Fin (1 + t) × Fin.Fin (1 + s)) →  neck-value-f (  neck-value-f⁻¹ {e}  x) ≡ x
  neck-value-id₁ {e} (x , y) with  neck-value-f⁻¹ {e} (x , y) | inspect  (neck-value-f⁻¹ {e})  (x , y)
  neck-value-id₁ {e} (x , y) | (._ , e#e₁) , (._ , e₁#e₂) | [ refl ] rewrite Inverse.right-inverse-of (GP-L e) x | Inverse.right-inverse-of (GP-P (Subset.elem (Inverse.from (GP-L e) ⟨$⟩ x)))  y = refl


  neck-value-bij : ∀ {e} → Inverse (PropEq.setoid (Neck e)) (PropEq.setoid (Fin.Fin (1 + t) × Fin.Fin (1 + s)))
  neck-value-bij {e} = record { to = record { _⟨$⟩_ = neck-value-f ; cong = cong neck-value-f } ;
                                from = record { _⟨$⟩_ = neck-value-f⁻¹ ; cong = cong neck-value-f⁻¹ } ;
                                inverse-of = record { left-inverse-of = neck-value-id₀ ; right-inverse-of = neck-value-id₁ } }


  
  neck-bij : ∀ {e f e' f' ≥1 ≥1'} → Inverse (PropEq.setoid (Neck e)) (PropEq.setoid (Neck e'))
  neck-bij {e} {f} {e'} {f'} {≥1} {≥1'} = Function.Inverse.sym neck-value-bij ∘ helper ∘ neck-value-bij
    where
      helper : Inverse _ _
      helper = bij-such-that x y
        where x = Inverse.to neck-value-bij ⟨$⟩ neck⋆ e f {≥1}
              y = Inverse.to neck-value-bij ⟨$⟩ neck⋆ e' f'
  
  lem-neck-bij : ∀ {e f e' f' ≥1 ≥1'} → Inverse.to neck-bij ⟨$⟩ neck⋆ e f {≥1} ≡ neck⋆ e' f' {≥1'}
  lem-neck-bij {e} {f} {e'} {f'} {≥1} {≥1'} =  subst (_≡_ (neck-value-f⁻¹ (Inverse.to (bij-such-that x y) ⟨$⟩ x)))
                                                     (neck-value-id₀ (ppneck (sppc e' f')))
                                                     (cong neck-value-f⁻¹ (lem-bij-such-that x y))
    where x = neck-value-f (neck⋆ e f {≥1})
          y = neck-value-f (neck⋆ e' f')
   
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
                                ≡⟨ cong suc (PropEq.sym lem-len/2-ρ) ⟩
                              1 + ⌊ len (ppc as-c) /2⌋
                                ≤⟨ ⌊n/2⌋-mono (s≤s p) ⟩
                              (⌈ n /2⌉ ∎)
    where open Data.Nat.≤-Reasoning

  A₁-ρ : (e f : P) → ∃ (λ (ppc : ppchain e f) → ρ' ppc ≤ ⌊ n /2⌋)
  A₁-ρ e f = (proj₁ (A₁ (pt e) (pt f))) as-ppc ,
                    (begin
                      ρ' _
                         ≡⟨ PropEq.sym lem-len/2-ρ ⟩
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
  A₂-ρ : ∀ {e f} (ppc ppc' : Subset (ppchain e f) (λ z → ρ' z < ⌈ n /2⌉ × irred (z as-c))) →
                                                 ppc ≡ ppc'
  A₂-ρ (ppc , p) (ppc' , p') with 
                                  cong (λ x → Subset.elem x as-ppc) (A₂ (ppc as-c , (lem-ρ-len<n (proj₁ p) , proj₂ p))
                                  (ppc' as-c , (lem-ρ-len<n (proj₁ p') , proj₂ p')))
  ... | z rewrite lem-id₁ {ppc = ppc} | lem-id₁ {ppc = ppc'} | z = refl

   
  lem-neckl : {x y : P} {ppc : ppchain x y} {≥1 : True (1 ≤? ρ' ppc)} → ln (neck-e₁ (ppneck ppc)) ≡ 
                      (neck (ppc as-c))
  lem-neckl {ppc = [ e ]} = λ {}
  lem-neckl {ppc = _∶⟨_⟩∶_ ._ _ ppc {{e#e₁}} {{e₁#e₂}}} = refl
 
  T#sym : ∀ {e f} → True (e #? f) → True (f #? e)
  T#sym x = fromWitness (#sym (toWitness x))
 
  module 0<ρ<n/2 {e f : P} {≥1 : True (1 ≤? ρ e f)} {<n : True (suc (ρ e f) ≤? ⌈ n /2⌉)} where
    -- e₂ ≡ e₂⋆
    class-A-ρ : (nck : Neck e) → nck ≡ neck⋆ e f {≥1} → ρ (neck-e₂ nck) f ≡ pred (ρ e f)
    class-A-ρ ._ refl = trans
                                      (PropEq.sym (tailpp-ρ-shortest {ppc = sppc e f} refl))
                                      (lem-tailpp-ρ {ppc = sppc e f})

    -- e₂ ≢ e₂⋆ , e₂ ≢ e , e₁ ≡ e₁⋆
    class-B-ρ : (nck : Neck e) → (proj₁ nck) ≡ proj₁ (neck⋆ e f {≥1}) →
                           (neck-e₂ nck) ≢ (neck-e₂ (neck⋆ e f {≥1})) →
                           neck-e₂ nck ≢ e → ρ (neck-e₂ nck) f ≡ ρ e f
    class-B-ρ ((._ , e#e₁) , (e₂ , e₁#e₂)) refl e₂≢e₂⋆ c = ≤-≥⇒≡ is≤ (pred-mono (≰⇒> is≮))
      where open Data.Nat.≤-Reasoning
            e₂⋆ = (neck-e₂ (neck⋆ e f))
            e₁⋆ = (neck-e₁ (neck⋆ e f))

            is≤ : ρ e₂ f ≤ ρ e f
            is≤ = begin
                  ρ e₂ f
                    ≤⟨ sppc-ρ-shorter-than (e₂ ∶⟨ e₁⋆ ⟩∶ sppc e₂⋆ f)
                      {{T#sym e₁#e₂}} {{Subset.proof (proj₂ (neck⋆ e f))}} ⟩
                  suc (ρ e₂⋆ f)
                    ≡⟨  cong suc (class-A-ρ (neck⋆ e f) refl) ⟩
                  suc (pred (ρ e f))
                    ≡⟨ suc∘pred ⟩
                  (ρ e f ∎)

            is≮ : ρ e₂ f < ρ e f → ⊥
            is≮ is< = ⊥-elim (e₂≢e₂⋆ (cong (λ x → neck-e₂ (ppneck (Subset.elem x) {lem-ρ'≥ρ ≥1})) z))
                where ppc : ppchain e f
                      ppc = e ∶⟨ e₁⋆ ⟩∶ sppc e₂ f

                      <n/2 : ρ' ppc < ⌈ n /2⌉
                      <n/2 = begin
                               suc (suc (ρ e₂ f)) ≤⟨ s≤s is< ⟩
                               suc (ρ e f) ≤⟨ toWitness <n ⟩ (⌈ n /2⌉ ∎)
                           
                      ppc-shortest : (ppc as-c) is-shortest
                      ppc-shortest rewrite lem-id₀ {c = sc (pt e₂) (pt f)} |
                                           lem-2xρ-lambda {e₂} {f} |
                                           lem-2xρ-lambda {e} {f} |
                                           solve 1 (λ x →
                                                   (con 2 :+ x :+ (x :+ con 0)
                                                        := con 1 :+ x :+ (con 1 :+ x :+ con 0)))
                                                 refl (ρ e₂ f)
                                   = ≤-≥⇒≡ (m≤m {2} *-mono is<) (m≤m {2} *-mono (sppc-ρ-shorter-than ppc))

                      ppc-irred : irred (ppc as-c)
                      ppc-irred = λ {a} {b} x → shortest-irred {pt e} {pt f} (ppc as-c) ppc-shortest {a} {b} x

                      z = A₂-ρ (ppc , (<n/2 , ppc-irred )) (sppc e f , (toWitness <n , sppc-irred))
    
    
    class-C₀-ρ : (nck : Neck e) → neck-e₁ nck ≢ neck-e₁ (neck⋆ e f) → neck-e₂ nck ≢ e → (ρ e f) < ⌈ (pred (n)) /2⌉ →  ρ (neck-e₂ nck) f ≡ 1 + ρ e f
    class-C₀-ρ ((e₁ , e#e₁) , (e₂ , e₁#e₂)) neck≢ e₂≢e <n/2 = ≤-≥⇒≡ is≤ (≰⇒> is≮)
      where open Data.Nat.≤-Reasoning
            .e₁#e : True ( ln e₁ #? pt e )
            e₁#e = T#sym e#e₁

            .e₂#e₁ : True ( pt e₂ #? ln e₁ )
            e₂#e₁ = T#sym e₁#e₂

            is≤ : ρ e₂ f ≤ 1 + ρ e f
            is≤ = sppc-ρ-shorter-than (e₂ ∶⟨ e₁ ⟩∶ sppc e f)

            pt-inj : ∀ {x y} → pt x ≡ pt y → x ≡ y
            pt-inj refl = refl
  

            ln-inj : ∀ {x y} → ln x ≡ ln y → x ≡ y
            ln-inj refl = refl

            e₁≢e₁⋆ : ∀ {x y} {ρxy≥1 : True (1 ≤? ρ x y)} → (neck≢ : e₁ ≢ neck-e₁ (neck⋆ x y)) → (ln e₁) ≢ ln (neck-e₁ (neck⋆ x y))
            e₁≢e₁⋆ neck≢ = λ x → neck≢ (ln-inj x)

            ¬e₁#e₁⋆ : ∀ {x y} {ρxy≥1 : True (1 ≤? ρ x y)} → (neck≢ : e₁ ≢ neck-e₁ (neck⋆ x y)) → (ln e₁) # ln (neck-e₁ (neck⋆ x y)) → ⊥
            ¬e₁#e₁⋆ {x} {y} {ρxy≥1} neck≢ = λ x → IP-ln (fromWitnessFalse ((e₁≢e₁⋆ {ρxy≥1 = ρxy≥1}) neck≢)) (fromWitness x)

            ¬e₁#neck : ∀ {x y} {ρxy≥1 : True (1 ≤? ρ x y)} → (neck≢ : e₁ ≢ neck-e₁ (neck⋆ x y {ρxy≥1})) → (ln e₁) #  neck (sc (pt x) (pt y)) → ⊥
            ¬e₁#neck {a} {b} {ρxy≥1} neck≢ = λ x → ((¬e₁#e₁⋆ {ρxy≥1 = ρxy≥1}) (neck≢)) (subst (_#_ (ln e₁)) (PropEq.sym (lem-neckl {ppc = sppc a b})) (subst (λ x₁ → ln e₁ # neck x₁) (PropEq.sym (lem-id₀ {c = sc (pt a) (pt b)})) x))

            c₂ : chain (ln e₁) (pt f)
            c₂ = _∷_ (ln e₁) {{fromWitnessFalse (λ ())}} (sc (pt e) (pt f))

            c₂-len : len c₂ < n
            c₂-len = begin
                       2 + lambda (pt e) (pt f) ≡⟨ cong (_+_ 2) lem-2xρ-lambda ⟩
                       2 + 2 * ρ e f ≡⟨
                       solve 1 (λ y → con 2 :+ con 2 :* y := con 2 :* (con 1 :+ y)) refl
                       (ρ e f)
                       ⟩
                       2 * (1 + ρ e f) ≤⟨ m≤m {2} *-mono <n/2 ⟩
                       2 * ⌈ (pred (n)) /2⌉ ≤⟨ lem-2x⌈n/2⌉ ⟩ (n ∎)

            c₂-irred : irred c₂
            c₂-irred = irred-∷ (ln e₁) (sc (pt e) (pt f) )
                       {fromWitness
                         (begin 2 ≤⟨ m≤m {2} *-mono toWitness ≥1 ⟩
                           _ ≡⟨ PropEq.sym lem-2xρ-lambda ⟩
                         (lambda (pt e) (pt f) ∎))}
                         (¬e₁#neck  {ρxy≥1 = ≥1} (neck≢))
                                   (shortest-irred (sc (pt e) (pt f)) refl)
            ρ<⇒λ< : ∀ {x y x' y'} → ρ x y ≤ ρ x' y' → lambda (pt x) (pt y) ≤ lambda (pt x') (pt y')
            ρ<⇒λ< {x} {y} {x'} {y'} ρ<  rewrite lem-2xρ-lambda {x} {y} | lem-2xρ-lambda {x'} {y'}  = m≤m {2} *-mono ρ<

            is≮ : ρ e₂ f ≤ ρ e f → ⊥
            is≮ is< with (neck (sc (pt e₂) (pt f))) ≟ (ln e₁)

            is≮ is< | yes p = helper (proj₁ (proj₂ c)) (cong len (cong Subset.elem z))
              where c : Σ (chain (ln e₁) (pt f)) (λ t → (len t < len c₂) × irred t)
                    c rewrite (PropEq.sym p) = (tail (sc (pt e₂) (pt f))) ,
                              s≤s (begin
                                len (tail (sc (pt e₂) (pt f)))
                                  ≡⟨ (lem-tail-len {c = sc (pt e₂) (pt f)}) ⟩
                                pred (lambda (pt e₂) (pt f))
                                  ≤⟨ ≤⇒pred≤ _ _ m≤m ⟩
                                lambda (pt e₂) (pt f)
                                  ≤⟨ ρ<⇒λ< is< ⟩
                                (len (sc (pt e) (pt f)) ∎)) ,
                                (shortest-irred (tail (sc (pt e₂) (pt f))) (tail-shortest refl))
                    z = A₂ ((proj₁ c) ,
                           ((<-trans (proj₁ (proj₂ c)) c₂-len) ,
                                     proj₂ (proj₂ c))) (c₂ , (c₂-len , c₂-irred))
                    helper : ∀ {x y} → x < y → x ≡ y  → ⊥
                    helper {zero} () refl
                    helper {suc x} q refl = helper (pred-mono q) refl

            is≮ is< | no ¬p  with 1 ≤? ρ e₂ f
            is≮ is< | no ¬p | yes p = e₂≢e (pt-inj (cong (λ x → neck (Subset.elem x)) z))
              where c : Subset (chain (ln e₁) (pt f)) (λ t → (len t < n) × irred t)
                    c =  _∷_ (ln e₁) {{fromWitnessFalse (λ ())}} (sc (pt e₂) (pt f)) ,
                           (begin
                         2 + lambda (pt e₂) (pt f) ≤⟨ s≤s (s≤s (ρ<⇒λ< is<)) ⟩
                         2 + lambda (pt e) (pt f) ≤⟨ c₂-len ⟩ (n ∎)) , 
                         irred-∷ (ln e₁) (sc (pt e₂) (pt f))
                         {fromWitness
                         (begin 2 ≤⟨ m≤m {2} *-mono p ⟩
                           _ ≡⟨ PropEq.sym lem-2xρ-lambda ⟩
                           (lambda (pt e₂) (pt f) ∎))}
                           (λ x → ¬e₁#neck {ρxy≥1 = fromWitness p}
                           (λ x₁ → ¬p (trans
                           (trans (cong neck (PropEq.sym (lem-id₀ {c = sc (pt e₂) (pt f)})))
                           (PropEq.sym (lem-neckl {ppc = sppc e₂ f})))
                           (cong ln (PropEq.sym x₁))))
                           x)
                           (shortest-irred (sc (pt e₂) (pt f)) refl)

                    z =  A₂ c (c₂ , (c₂-len , c₂-irred))
            is≮ is< | no ¬p₁ | no ¬p rewrite PropEq.sym  (ρ≡0⇒e≡f {e₂} {f} (<1⇒≡0  (≰⇒> ¬p))) =
                                  helper {1} {len (proj₁ c)}
                                    (begin
                                      2 ≤⟨ m≤m {2} *-mono toWitness ≥1 ⟩
                                      2 * ρ e f
                                        ≡⟨ PropEq.sym lem-2xρ-lambda ⟩
                                      lambda (pt e) (pt f)
                                        ≤⟨ ≤′⇒≤ (≤′-step ≤′-refl) ⟩
                                      suc _
                                        ≡⟨ PropEq.sym (cong len (cong Subset.elem z)) ⟩
                                      (len (proj₁ c) ∎))
                                    (PropEq.sym (proj₁ (proj₂ c)))
              where c : Σ (chain (ln e₁) (pt f)) (λ t → (len t ≡ 1) × irred t)
                    c rewrite PropEq.sym (ρ≡0⇒e≡f {e₂} {f}
                                         (<1⇒≡0  (≰⇒> ¬p))) = _∷_ (ln e₁)
                                           {{fromWitnessFalse (λ ())}}
                                             [ pt e₂ ] , refl , tt

                    z : _
                    z = (A₂ ((proj₁ c) , ((begin
                                         suc (len (proj₁ c))
                                           ≡⟨ cong suc (proj₁ (proj₂ c)) ⟩
                                         2 ≤⟨ s≤s (s≤s z≤n) ⟩ (n ∎)) ,
                        proj₂ (proj₂ c))) (c₂ , (c₂-len , c₂-irred)))
                    
                    helper : ∀ {x y} → x < y → x ≡ y  → ⊥
                    helper {zero} () refl
                    helper {suc x} q refl = helper (pred-mono q) refl

    class-C₁-ρ : (nck : Neck e) → neck-e₁ nck ≢ neck-e₁ (neck⋆ e f) → neck-e₂ nck ≢ neck-e₂ (neck⋆ e f) →
                 neck-e₂ nck ≢ e → (ρ e f) ≡ ⌈ (pred (n)) /2⌉ →
                 ρ (neck-e₂ nck) f ≡ ρ e f

    class-C₁-ρ  ((e₁ , e#e₁) , (e₂ , e₁#e₂)) neck≢ e₂≢e₂⋆ e₂≢e ≡n/2 = ≤-≥⇒≡ is≤ (pred-mono (≰⇒> is≮))
      where open Data.Nat.≤-Reasoning
            e₂⋆ = (neck-e₂ (neck⋆ e f))
            e₁⋆ = (neck-e₁ (neck⋆ e f))
            
            is≤ : ρ e₂ f ≤ ρ e f
            is≤ = begin
                  ρ e₂ f
                    ≤⟨ A₁'-ρ ⟩
                  ⌊ n /2⌋
                    ≡⟨ PropEq.sym ≡n/2 ⟩
                  (ρ e f ∎)

            is≮ : ρ e₂ f < ρ e f → ⊥
            is≮ is< = ⊥-elim (e₂≢e₂⋆ (cong (λ x → neck-e₂ (ppneck (Subset.elem x) {lem-ρ'≥ρ ≥1})) z))
                where ppc : ppchain e f
                      ppc = ((e ∶⟨ e₁ ⟩∶ sppc e₂ f)) 

                      <n/2 : ρ' ppc < ⌈ n /2⌉
                      <n/2 = begin
                               suc (suc (ρ e₂ f)) ≤⟨ s≤s is< ⟩
                               suc (ρ e f) ≤⟨ toWitness <n ⟩ (⌈ n /2⌉ ∎)
                           
                      ppc-shortest : (ppc as-c) is-shortest
                      ppc-shortest rewrite lem-id₀ {c = sc (pt e₂) (pt f)} |
                                           lem-2xρ-lambda {e₂} {f} |
                                           lem-2xρ-lambda {e} {f} |
                                           solve 1 (λ x →
                                                   (con 2 :+ x :+ (x :+ con 0)
                                                        := con 1 :+ x :+ (con 1 :+ x :+ con 0)))
                                                 refl (ρ e₂ f)
                                   = ≤-≥⇒≡ (m≤m {2} *-mono is<) (m≤m {2} *-mono (sppc-ρ-shorter-than ppc))

                      ppc-irred : irred (ppc as-c)
                      ppc-irred = λ {a} {b} x → shortest-irred {pt e} {pt f} (ppc as-c) ppc-shortest {a} {b} x

                      z = A₂-ρ (ppc , (<n/2 , ppc-irred )) (sppc e f , (toWitness <n , sppc-irred))
    

  module ρ≡n/2 {e f : P} {n-even : Even (n)} {≡n/2 : True ( ⌈ (n) /2⌉ ℕ≟ ρ e f)} where

    open import Lemma2-1

    private
      λ≡n : lambda (pt e) (pt f) ≡ n
      λ≡n = PropEq.sym (
            begin
              n
                ≡⟨ PropEq.sym (lem-2x⌈n/2⌉-even n-even) ⟩
              2 * ⌈ n /2⌉ 
                ≡⟨ cong (_*_ 2) (toWitness ≡n/2) ⟩
              2 * ρ e f
                ≡⟨ PropEq.sym lem-2xρ-lambda ⟩
              (lambda (pt e) (pt f) ∎))
        where open ≡-Reasoning

      chain-with-neck : (nck : Neck e) → chain (pt e) (pt f)
      chain-with-neck nck = proj₁ $ Inverse.from (I e (pt f) λ≡n) ⟨$⟩ l#e
        where l#e : L# e
              l#e = (neck-e₁ nck) , neck-e#e₁ nck

      len-cwc≡n : (nck : Neck e) → len (chain-with-neck nck) ≡ n
      len-cwc≡n nck = proj₂ $ Inverse.from (I e (pt f) λ≡n) ⟨$⟩ l#e
        where l#e : L# e
              l#e = (neck-e₁ nck) , neck-e#e₁ nck

      ppc-with-neck : (nck : Neck e) → ppchain e f
      ppc-with-neck nck = chain-with-neck nck as-ppc

      ρef≥1 : ρ e f ≥ 1
      ρef≥1 = begin 1 ≤⟨ s≤s z≤n ⟩ ⌈ n /2⌉ ≡⟨ toWitness ≡n/2 ⟩ (ρ e f ∎)
        where open Data.Nat.≤-Reasoning

      ρ'ppc≡n : (nck : Neck e) → ρ' (ppc-with-neck nck) ≡ ⌈ (n) /2⌉
      ρ'ppc≡n nck rewrite PropEq.sym (lem-lambda/2-ρ {e} {f}) |
                          PropEq.sym (lem-len/2-ρ {ppc = ppc-with-neck nck}) |
                          lem-id₀ {c = sc (pt e) (pt f)} |
                          lem-id₀ {c = chain-with-neck nck} =
                            trans (cong ⌊_/2⌋ lenc≡n) (lem-even⇒⌊≡⌋ n-even)
        where l#e : L# e
              l#e = (neck-e₁ nck) , neck-e#e₁ nck
              lenc≡n = proj₂ $ Inverse.from (I e (pt f) λ≡n) ⟨$⟩ l#e
      
      ρ'ppc≥1 : (nck : Neck e) → ρ' (ppc-with-neck nck) ≥ 1
      ρ'ppc≥1 nck = begin 1 ≤⟨ s≤s z≤n ⟩ ⌈ (n) /2⌉ ≡⟨ PropEq.sym (ρ'ppc≡n nck) ⟩ (ρ' (ppc-with-neck nck) ∎)
        where open Data.Nat.≤-Reasoning

      ppc-shortest : (nck : Neck e) → (ppc-with-neck nck) is-ρ-shortest
      ppc-shortest nck = trans (ρ'ppc≡n nck) (toWitness ≡n/2)

      e₂⋆ : (nck : Neck e) → P
      e₂⋆ nck = (neck-e₂ $ ppneck (ppc-with-neck nck) {fromWitness (ρ'ppc≥1 nck)})
    
    class-A₀-ρ : (nck : Neck e) → (neck-e₂ nck) ≡ (e₂⋆ nck) → ρ (neck-e₂ nck) f ≡ pred ⌈ (n) /2⌉
    class-A₀-ρ nck eq = begin
                       ρ e₂ f
                         ≡⟨ cong ((Function.flip ρ) f) eq ⟩
                       ρ (e₂⋆ nck) f
                         ≡⟨ PropEq.sym (tailpp-ρ-shortest (ppc-shortest nck)) ⟩
                       ρ' (tailpp (ppc-with-neck nck))
                         ≡⟨ lem-tailpp-ρ {ppc = ppc-with-neck nck} ⟩
                       pred (ρ' (ppc-with-neck nck))
                         ≡⟨ cong pred (ρ'ppc≡n nck) ⟩
                       (pred ⌈ n /2⌉ ∎)                                                                                
      where open ≡-Reasoning
            e₂ = neck-e₂ nck

    class-A₁-ρ :  (nck : Neck e) → (neck-e₂ nck) ≢ (e₂⋆ nck) → ρ (neck-e₂ nck) f ≡ ⌈ (n) /2⌉
    class-A₁-ρ nck neq = ≤-≥⇒≡ (begin _ ≤⟨ A₁'-ρ ⟩ ⌊ n /2⌋ ≡⟨ lem-even⇒⌊≡⌋ n-even ⟩ (⌈ n /2⌉ ∎)) (≰⇒> (λ x → ¬is< (s≤s x)))
      where open Data.Nat.≤-Reasoning
            e₁ = neck-e₁ nck
            e₂ = neck-e₂ nck
            
            ppc : ppchain e f
            ppc = ((e ∶⟨ e₁ ⟩∶ (sppc e₂ f)) {{neck-e#e₁ nck}} {{neck-e₁#e₂ nck}})
  
            ¬is< : suc (ρ (neck-e₂ nck) f) ≤ ⌈ (n) /2⌉ → ⊥
            ¬is< is< with suc (suc (ρ e₂ f)) ≤? ⌈ (n) /2⌉

            ¬is< is< | yes p = ¬<-≡ ρef<n/2 (sym (toWitness ≡n/2))
              where ρef<n/2 : ρ e f <  ⌈ (n) /2⌉
                    ρef<n/2 = begin
                              suc (ρ e f)
                                ≤⟨ s≤s (sppc-ρ-shorter-than ppc) ⟩
                                suc (suc (ρ e₂ f))
                                ≤⟨ p ⟩ (⌈ n /2⌉ ∎)
 
            ¬is< is< | no ¬p = neq e₂≡e₂⋆
              where ρ'ppc≡n/2 : ρ' ppc ≡ ⌈ (n) /2⌉ 
                    ρ'ppc≡n/2 = ≤-≥⇒≡ is< (≰⇒> (λ x → ¬p (s≤s x)))
      
                    len-ppc-as-c≡n : len (ppc as-c) ≡ n
                    len-ppc-as-c≡n rewrite
                                   lem-id₀ {c = sc (pt e₂) (pt f)} |
                                   (lem-2xρ-lambda {e₂} {f}) |
                                   sym (lem-2x⌈n/2⌉-even n-even) =
                                       trans (solve 1
                                         (λ x → con 2 :+ x :+ (x :+ con 0) :=
                                           con 1 :+ x :+ (con 1 :+ x :+ con 0))
                                               refl (ρ e₂ f)) (cong (_*_ 2) ρ'ppc≡n/2)

                    c≡ : ppc as-c ≡ chain-with-neck nck
                    c≡ = cong proj₁ (sym
                                         (Inverse.left-inverse-of (I e (pt f) λ≡n)
                                          (ppc as-c , len-ppc-as-c≡n)))
                    
                    ppc≡ : ppc ≡ ppc-with-neck nck
                    ppc≡ = trans (sym lem-id₁) (cong _as-ppc c≡)
      
                    e₂≡e₂⋆ : e₂ ≡ (e₂⋆ nck)
                    e₂≡e₂⋆ = cong neck-e₂ (cong (λ x → ppneck-gen x {fromWitness ρef≥1}) ppc≡)
                    
       
