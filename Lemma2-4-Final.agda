open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import Relation.Binary.PropositionalEquality as PropEq hiding (proof-irrelevance)

open import Data.Empty
open import Data.Unit hiding (_≤?_; _≤_; _≟_)

open import Data.Product 

open import Data.Bool hiding (_≟_)

open import Data.Nat renaming (_≟_ to _ℕ≟_)
--open Data.Nat.≤-Reasoning

--open import Function.Inverse
open import Data.Sum

open import Data.Nat.Properties
open SemiringSolver

open import Function hiding (_∘_)
open import Function.Equality hiding (_∘_) renaming (cong to Icong)
open import Function.Inverse renaming (sym to Isym; zip to Izip; id to Iid)
open import Function.LeftInverse hiding (_∘_)
import Function.Equivalence as FunEq

open import Function.Bijection hiding (_∘_)

import Data.Fin as F
import Data.Fin.Props as F

open import Function.Related.TypeIsomorphisms

import Relation.Binary.Sigma.Pointwise as SP

import Lemma2-4-Bij-A as bijA
import Lemma2-4-Bij-B as bijB


open import FinBijections

open import Data.Vec hiding ([_])

open import Misc

module Lemma2-4-Final where
  
  open import Lemma2-4 public

  lem₀ : ∀ {e f} → ρ e f ≡ 0 → F.Fin 0 ↔ (K e f 0)
  lem₀ {e} {f} ρ≡ = record {
                    to = record { _⟨$⟩_ = to ; cong = cong to } ;
                    from = record { _⟨$⟩_ = from ; cong = cong from } ;
                    inverse-of = record {
                      left-inverse-of = left-inverse-of ;
                      right-inverse-of = right-inverse-of } }
    where to : F.Fin 0 → (K e f 0)
          to ()

          from : K e f 0 → F.Fin 0
          from (nck , proof) = ⊥-elim (proj₁ proof (trans
                                                   (ρ≡0⇒e≡f $ proj₂ proof)
                                                   (sym $ ρ≡0⇒e≡f ρ≡)))

          left-inverse-of : ∀ x → from (to x) ≡ x
          left-inverse-of ()

          right-inverse-of : ∀ x → to (from x) ≡ x
          right-inverse-of (nck , proof) = ⊥-elim
                                             (proj₁ proof (trans 
                                                    (ρ≡0⇒e≡f $ proj₂ proof) 
                                                    (sym $ ρ≡0⇒e≡f ρ≡)))
  private
    lem-ρ-helper : ∀ {y z} → 2 + y ≤ z → z ≤ 1 + y → ⊥
    lem-ρ-helper {zero} {zero} () z≤n
    lem-ρ-helper {zero} {suc .0} (s≤s ()) (s≤s z≤n)
    lem-ρ-helper {suc y} {zero} () q
    lem-ρ-helper {suc y} {suc m} (s≤s p) (s≤s q) = lem-ρ-helper p q

  lem-ρ≤ : ∀ {e f} {nck : Neck e} → (ρ (neck-e₂ nck) f) > suc (ρ e f) → ⊥
  lem-ρ≤ {e} {f} {nck} with (sppc-ρ-shorter-than
                           ((neck-rev nck) ∷ sppc e f))
  ... | a = λ x → lem-ρ-helper {ρ e f} {ρ (neck-e₂ nck) f} x a
         
  lem-ρ≥ : ∀ {e f} {nck : Neck e} → suc (ρ (neck-e₂ nck) f) < (ρ e f) → ⊥
  lem-ρ≥ {e} {f} {nck} x with sppc-ρ-shorter-than
                           (nck ∷ sppc (neck-e₂ nck) f)
  ... | a = lem-ρ-helper {ρ (neck-e₂ nck) f} {ρ e f} x a

  lem-ρ≥-bij : ∀ {e f i} → i > suc (ρ e f) →
               F.Fin 0 ↔ (K e f i)
  lem-ρ≥-bij {e} {f} {i} ρ> =
    record {
      to = record { _⟨$⟩_ = to ; cong = cong to } ;
      from = record { _⟨$⟩_ = from ; cong = cong from } ;
      inverse-of = record { left-inverse-of = left-inverse-of ; 
                            right-inverse-of = right-inverse-of } }
    where to : F.Fin 0 → (K e f i)
          to ()
  
          from : (K e f i) → F.Fin 0
          from (nck , proof) = ⊥-elim (lem-ρ≤ {nck = nck}
                                      (subst (λ z → z > suc (ρ e f))
                                                (sym $ proj₂ proof) ρ>))

          left-inverse-of : ∀ x → from (to x) ≡ x
          left-inverse-of ()

          right-inverse-of : ∀ x → to (from x) ≡ x
          right-inverse-of (nck , proof) =
            ⊥-elim (lem-ρ≤ {nck = nck} (subst (λ z → z > suc (ρ e f))
                                       (sym $ proj₂ proof) ρ>))

  lem-ρ≤-bij : ∀ {e f i} → suc i < ρ e f → F.Fin 0 ↔ (K e f i)
  lem-ρ≤-bij {e} {f} {i} ρ< =
    record { to = record { _⟨$⟩_ = to ; cong = cong to } ;
             from = record { _⟨$⟩_ = from ; cong = cong from } ;
             inverse-of = record { left-inverse-of = left-inverse-of ;
                                   right-inverse-of = right-inverse-of } }
    where to : F.Fin 0 → (K e f i)
          to ()
           
          from : (K e f i) → F.Fin 0
          from (nck , proof) =
            ⊥-elim (lem-ρ≥ {nck = nck} (subst (λ z → suc z < ρ e f)
                           (sym $ proj₂ proof) ρ<))

          left-inverse-of : ∀ x → from (to x) ≡ x
          left-inverse-of ()

          right-inverse-of : ∀ x → to (from x) ≡ x
          right-inverse-of (nck , proof) =
            ⊥-elim (lem-ρ≥ {nck = nck} (subst (λ z → suc z < ρ e f)
                                                 (sym $ proj₂ proof) ρ<))

  lem₁ : ∀ {e f i} → i > ⌊ n /2⌋ → F.Fin 0 ↔ (K e f i)
  lem₁ {e} {f} {i} i> =
    record { to = record { _⟨$⟩_ = to ; cong = cong to } ;
             from = record { _⟨$⟩_ = from ; cong = cong from } ;
             inverse-of = record { left-inverse-of = left-inverse-of ;
                                   right-inverse-of = right-inverse-of } }
    where open Data.Nat.≤-Reasoning
          to : F.Fin 0 → (K e f i)
          to ()
          
          helper : {nck : Neck e} → ρ (neck-e₂ nck) f ≡ i → ⊥
          helper {nck} eq =
            ⊥-elim (≤⇒≯ (A₁'-ρ {neck-e₂ nck} {f})
              (subst (λ z → z > ⌊ n /2⌋) (sym eq) i>))

          from : (K e f i) → F.Fin 0
          from (nck , proof) = ⊥-elim (helper {nck} (proj₂ proof))

          left-inverse-of : ∀ x → from (to x) ≡ x
          left-inverse-of ()

          right-inverse-of : ∀ x → to (from x) ≡ x
          right-inverse-of (nck , proof) =
            ⊥-elim (helper {nck} (proj₂ proof))

  k : (r i : ℕ) → Σ ℕ (λ x → ∀ (e f : P)
      (eq : (ρ e f) ≡ r) → (F.Fin x) ↔ (K e f i))

  k zero zero = 0 , (λ e f ρ≡ → lem₀ ρ≡) -- 0
  k zero (suc zero) = ((1 + t) * s) , (λ e f eq → (Isym $ bijA.bij₀ eq) ∘
                                           (Isym $ bijB.Bijection₀.bij e f))
  k zero (suc (suc i)) = 0 , (λ e f eq → lem-ρ≥-bij (s≤s (s≤s
                             (begin ρ e f ≡⟨ eq ⟩ 0 ≤⟨ z≤n ⟩ (i ∎)))))
    where open Data.Nat.≤-Reasoning

  k (suc r) i with ⌊ n /2⌋ ≤? (suc r)
  k (suc r) i | yes p with suc r ℕ≟ ⌊ n /2⌋
  k (suc r) i | yes p | no ¬p = 0 , (λ e f eq →
              ⊥-elim (≤⇒≯ (A₁'-ρ {e} {f}) (≤-≢⇒< (subst
                (λ z → ⌊ n /2⌋ ≤ z) (sym eq) p)
                  (λ x → ¬p (trans (sym eq) (sym x))))))
  k (suc r) i | yes p | yes p₁ with compare (suc r) i
    -- Boundary case begin
  k (suc r) .(suc (suc (r + 0))) | yes p | yes p₁ | less .(suc r) zero =
    0 , (λ e f eq → lem₁ (begin
                         suc ⌊ n /2⌋
                           ≤⟨ s≤s p ⟩
                         suc (suc r)
                           ≡⟨ cong suc (cong suc (+-comm {0} {r})) ⟩
                         (suc (suc (r + 0)) ∎)))
    where open Data.Nat.≤-Reasoning

  k (suc r) .(suc (suc (r + suc k))) | yes p | yes p₁ | less .(suc r) (suc k) 
         = 0 , (λ e f eq → lem-ρ≥-bij
                  (begin suc (suc (ρ e f))
                    ≡⟨ cong suc (cong suc eq) ⟩
                  suc (suc (suc r))
                    ≤⟨ s≤s (s≤s helper) ⟩
                  (suc (suc (r + suc k)) ∎)))
        where open Data.Nat.≤-Reasoning
              helper : ∀ {k} → suc r ≤ r + suc k
              helper {zero} rewrite  +-comm {1} {r} = m≤m
              helper {suc k₁} rewrite  +-comm {1} {r} = m≤m {r} +-mono s≤s z≤n

  k (suc r) .(suc r) | yes p | yes p₁ | equal .(suc r) with parity n
  ... | isEven x = (1 + t ) * (pred s) , (λ e f eq →
                   (Isym $ bijA.bij₆ eq
                     {≡predn/2 =
                       (fromWitness (trans p₁
                                    (lem-even⇒⌊≡⌋ x)))} {evenn = x}) ∘
                   (Isym $ bijB.Bijection₆.bij e f x
                     (fromWitness (trans (trans eq p₁)
                       (lem-even⇒⌊≡⌋ x))) (ρ≡n/2.e₂⋆# {n-even = x} 
                         {≡n/2 = fromWitness (trans eq
                           (trans p₁ (lem-even⇒⌊≡⌋ x)))} )
                   (λ {l#e} →
                     ρ≡n/2.lem-e₂⋆ {n-even = x}
                     {≡n/2 = fromWitness (trans eq (trans p₁
                                                (lem-even⇒⌊≡⌋ x)))}
                                                              {l#e = l#e})))
  
  ... | isOdd (oddSuc x) = pred s + t * s ,
                           (λ e f eq → Isym
                             (bijA.bij₄ eq {≡predn/2 = fromWitness p₁}
                                           {oddn = oddSuc x}) ∘
                             (Isym $ bijB.Bijection₄.bij e f (neck⋆ e f)
                                     (lem-neck⋆ {<n = fromWitness
                                       (begin
                                         suc (ρ e f) ≡⟨ cong suc eq ⟩
                                         suc (suc r) ≡⟨ cong suc p₁ ⟩
                                         suc (suc ⌊ suc nn /2⌋)
                                           ≡⟨ cong (_+_ 2) (helper x) ⟩
                                         (suc (suc ⌊ nn /2⌋) ∎)) })))
    where open Data.Nat.≤-Reasoning
          helper : ∀ {x} → Odd (suc x) →  ⌊ suc x /2⌋ ≡ ⌊ x /2⌋
          helper {zero} ox = refl
          helper {suc zero} (oddSuc ())
          helper {suc (suc x₁)} (oddSuc ox) = cong suc (helper ox)

  k (suc .(i + 0)) i | yes p | yes p₁ | greater .i zero
    with ⌊ n /2⌋ ≤? (i + 0)
  ... | yes q = 0 , (λ e f eq →
        ⊥-elim (≤⇒≯ (A₁'-ρ {e} {f}) (begin
                                    suc ⌊ n /2⌋ ≤⟨ s≤s q ⟩
                                    suc (i + 0) ≡⟨ sym eq ⟩
                                    (ρ e f ∎))))
    where open Data.Nat.≤-Reasoning

  ... | no ¬q with parity n 
  ... | isEven x = (1 + t) ,
                   (λ e f eq →
                   (Isym $ bijA.bij₅ {e} {f} 
                     (trans eq (cong suc (+-comm {i} {0})))
                       {≡predn/2 = (fromWitness (trans
                         (trans
                           (cong suc (+-comm {0} {i})) p₁)
                             (lem-even⇒⌊≡⌋ x)))} {evenn = x})
                               ∘ (Isym $ bijB.Bijection₅.bij e f
                                 (ρ≡n/2.e₂⋆# {n-even = x}
                                   {≡n/2 = fromWitness (trans eq
                                         (trans p₁ (lem-even⇒⌊≡⌋ x)))})))

  ... | isOdd x = 1 ,
                (λ e f eq →
                (Isym $
                  bijA.bij₁ (subst (λ z → ρ e f ≡ suc z)
                                   (+-comm {i} {0}) eq)
                                     {<n = fromWitness helper} ) ∘
                  (Isym $ bijB.Bijection₁.bij e f (neck⋆ e f)))
      where open Data.Nat.≤-Reasoning
            helper₁ : ∀ {x} → Odd x → suc ⌊ x /2⌋ ≡ ⌈ x /2⌉
            helper₁ {zero} ()
            helper₁ {suc zero} x₂ = refl
            helper₁ {suc (suc x₁)} (oddSuc x₂) = cong suc (helper₁ x₂)

            helper : suc (suc i) ≤ ⌈ n /2⌉
            helper = begin
                     suc (suc i)
                       ≡⟨ cong suc (cong suc (+-comm {0} {i})) ⟩
                     suc (suc (i + 0))
                       ≤⟨ s≤s (≰⇒> ¬q) ⟩
                     suc ⌊ n /2⌋ ≡⟨ helper₁ x ⟩
                       (⌈ n /2⌉ ∎)

  k (suc .(i + suc k)) i | yes p | yes p₁ | greater .i (suc k) =
         0 , (λ e f eq → lem-ρ≤-bij
           (begin suc (suc i)
                      ≤⟨ s≤s helper ⟩
                  suc (i + suc k)
                      ≡⟨ sym eq ⟩
                  (ρ e f ∎)))
    where open Data.Nat.≤-Reasoning  
          helper : ∀ {i k} → suc i ≤ i + suc k
          helper {zero} = s≤s z≤n
          helper {suc i₁} = s≤s helper
  -- Boundary case end

  
  k (suc r) i | no ¬p  with compare (suc r) i

  k (suc r) .(suc (suc (r + 0))) | no ¬p | less .(suc r) zero =
    t * s , (λ e f eq →
            (Isym $
              bijA.bij₃ (subst (λ z → ρ e f ≡ suc z)
                        (sym $ +-comm {r} {0}) eq)
                          {<predn = fromWitness <predn}) ∘
              (Isym $ bijB.Bijection₃.bij e f (neck⋆ e f)))
                              
    where open Data.Nat.≤-Reasoning

          <predn : (suc (suc (r + 0)) ≤ suc ⌊ suc nn /2⌋)
          <predn = begin
                     suc (suc (r + 0))
                       ≡⟨ cong suc (cong suc (+-comm {r} {0})) ⟩
                     suc (suc r) ≤⟨ ≰⇒> ¬p ⟩ (suc ⌊ suc nn /2⌋ ∎)
  
          ρef≥1 : ∀ {e f} → ρ e f ≡ suc r → ρ e f ≥ 1
          ρef≥1 eq = subst (λ z → 1 ≤ z) (sym eq) (s≤s (z≤n {r}))

  k (suc r) .(suc (suc (r + suc k))) | no ¬p | less .(suc r) (suc k) = 0 ,
                  (λ e f eq → lem-ρ≥-bij (
                    begin
                      suc (suc (ρ e f))
                        ≡⟨ cong suc (cong suc eq) ⟩
                      suc (suc (suc r))
                        ≤⟨ s≤s (s≤s helper) ⟩
                      (suc (suc (r + suc k)) ∎)))
        where open Data.Nat.≤-Reasoning
              helper : ∀ {k} → suc r ≤ r + suc k
              helper {zero} rewrite  +-comm {1} {r} = m≤m
              helper {suc k₁} rewrite  +-comm {1} {r} =
                                              m≤m {r} +-mono s≤s z≤n

  k (suc r) .(suc r) | no ¬p | equal .(suc r) = (pred s) ,
                  (λ e f eq →
                  (Isym $ bijA.bij₂ eq {<predn = fromWitness (≰⇒> ¬p)}) ∘
                              (Isym $ bijB.Bijection₂.bij e f (neck⋆ e f)
                                (lem-neck⋆ {e} {f}
                                  {fromWitness (ρef≥1 eq)}
                                  {<n = fromWitness (ρef<n eq)})))
    where open Data.Nat.≤-Reasoning
          ρef≥1 : ∀ {e f} → ρ e f ≡ suc r → ρ e f ≥ 1
          ρef≥1 eq = subst (λ z → 1 ≤ z) (sym eq) (s≤s (z≤n {r}))

          ρef<n : ∀ {e f} → ρ e f ≡ suc r → suc (ρ e f) ≤ ⌈ n /2⌉
          ρef<n {e} {f} eq =
            begin
              suc (ρ e f)
                ≤⟨ subst (λ z → suc z ≤ suc ⌊ suc nn /2⌋) (sym eq) (≰⇒> ¬p) ⟩
              ⌊ n /2⌋ ≤⟨ ⌊≤⌉ n ⟩ (⌈ n /2⌉ ∎)
          
  k (suc .(i + 0)) i | no ¬p | greater .i zero = 1 ,
                       (λ e f eq → (Isym $
                         bijA.bij₁ (subst (λ z → ρ e f ≡ suc z) 
                                          (+-comm {i} {0}) eq)
                           {<n = fromWitness helper})
                             ∘ (Isym $ bijB.Bijection₁.bij e f (neck⋆ e f)))
    where open Data.Nat.≤-Reasoning
          helper : suc (suc i) ≤ ⌈ n /2⌉
          helper = begin
                   suc (suc i)
                     ≡⟨ cong suc (cong suc (+-comm {0} {i})) ⟩
                   suc (suc i + 0) ≤⟨ ≰⇒> ¬p ⟩
                     ⌊ n /2⌋ ≤⟨ ⌊≤⌉ n ⟩ (⌈ n /2⌉ ∎)

  k (suc .(i + suc k)) i | no ¬p | greater .i (suc k) = 0 ,
             (λ e f eq → lem-ρ≤-bij (
                begin
                  suc (suc i)
                    ≤⟨ s≤s (s≤s (m≤m+n i k)) ⟩ 
                  suc (suc (i + k))
                    ≡⟨ cong suc helper ⟩ 
                  suc (i + suc k) 
                    ≡⟨ sym eq ⟩ (ρ e f ∎)))
    where open Data.Nat.≤-Reasoning
          helper : suc (i + k) ≡ i + suc k
          helper = solve 2
                   (λ x y →
                     con 1 :+ (x :+ y) := x :+ (con 1 :+ y)) refl i k
  
  M : (e f : P) (q : ℕ) → Set
  M e f q = Σ (ppchain e f) (λ ppc → ρ' ppc ≡ q)


  ppneck′ : ∀ {e f q} → M e f (suc q) → Neck e
  ppneck′ ([ e ] ,  ())
  ppneck′ ((e₁ ∶ e#e₁ , e₂ ∶ e₁#e₂) ∷ ppc , ≡sucq) = (e₁ ∶ e#e₁) ,(e₂ ∶ e₁#e₂)
    where open Data.Nat.≤-Reasoning

  pptail′ :  ∀ {e f q} → (x : Σ (ppchain e f) (λ ppc → ρ' ppc ≡ suc q)) →
                  Σ (ppchain (neck-e₂ $ ppneck′ x)  f) (λ ppc′ → ρ' ppc′ ≡ q)
  pptail′ ([ e ] ,  ())
  pptail′ ((e₁ ∶ e#e₁ , e₂ ∶ e₁#e₂) ∷ ppc , refl) = ppc , refl

  ppc-app : ∀ {e f q} → (x : Σ (Neck e) (λ nck → M (neck-e₂ nck) f q)) →
              Σ (ppchain e f) (λ ppc → ρ' ppc ≡ suc q)
  ppc-app {e} (nck , (ppc , refl  )) = nck ∷ ppc , refl

  lem-ppc-app : ∀ {e f q} (x : M e f (suc q)) →
                  ppc-app ((ppneck′ x) , (pptail′ x)) ≡ x
  lem-ppc-app ([ e ] , ())
  lem-ppc-app ((e₁ ∶ e#e₁ , e₂ ∶ e₁#e₂) ∷ ppc , refl) = refl

  lem-pptail′ : ∀ {e f q} → (x : Σ (Neck e) (λ nck → M (neck-e₂ nck) f q)) →
                       ((ppneck′ (ppc-app x)) , (pptail′ (ppc-app x))) ≡ x
  lem-pptail′ (_ , _ , refl) = refl

  M≡ : (e f : P) (q : ℕ)  → Set
  M≡ e f q = Σ (M e f (suc q)) (λ x → neck-e₂ (ppneck′ x) ≡ e)
    where open Data.Nat.≤-Reasoning

  M≢ : (e f : P) (q : ℕ) → Set
  M≢ e f q = Σ (M e f (suc q)) (λ x → neck-e₂ (ppneck′ x) ≢ e)
    where open Data.Nat.≤-Reasoning

  A₁'-ρ-ceil : ∀ {e₂ f} → ρ e₂ f ≤ ⌈ n /2⌉
  A₁'-ρ-ceil {e₂} {f} = begin ρ e₂ f
                                ≤⟨ A₁'-ρ {e₂} {f} ⟩
                              ⌊ n /2⌋ ≤⟨ ⌊≤⌉ n ⟩ (⌈ n /2⌉ ∎)
    where open Data.Nat.≤-Reasoning

  bij₋₁ : {A : Set} → (Σ A (λ _ → ⊤)) ↔ A
  bij₋₁ {A} = record {
                     to = record { _⟨$⟩_ = proj₁ ; cong = cong _ } ;
                     from = record { _⟨$⟩_ = λ x → x , tt ; cong = cong _ } ;
                     inverse-of = record { left-inverse-of = λ x → refl ;
                                           right-inverse-of = λ x → refl } }

  bij₀ : ∀ {e f q} → (Σ (M e f (suc q)) (λ _ → ⊤)) ↔
                     (Σ (M e f (suc q)) (λ x → neck-e₂ (ppneck′ x) ≡ e ⊎
                                               neck-e₂ (ppneck′ x) ≢ e))
  bij₀ {e} {f} {q} =
    SP.↔ Iid (λ {x} →
      record { to = record { _⟨$⟩_ = to ; cong = cong to } ;
               from = record { _⟨$⟩_ = from {x} ; cong = cong from } ;
               inverse-of = record { left-inverse-of = λ _ → refl ;
                                     right-inverse-of = right-inverse-of } })
    where to : {x : M e f (suc q)} → ⊤ →
               neck-e₂ (ppneck′ x) ≡ e ⊎ neck-e₂ (ppneck′ x) ≢ e
          to {x} tt with pt (neck-e₂ (ppneck′ x)) ≟ pt e
          to tt | yes p = inj₁ (pt-inj p)
          to tt | no ¬p = inj₂ (λ x → ¬p (cong pt x))

          from : {x : M e f (suc q)} →
                 neck-e₂ (ppneck′ x) ≡ e ⊎ neck-e₂ (ppneck′ x) ≢ e → ⊤
          from _ = tt

          left-inverse-of : {x : M e f (suc q)} → ∀ z → from (to {x} z) ≡ z
          left-inverse-of x = refl

          right-inverse-of :{x : M e f (suc q)} → ∀ z → to (from {x} z) ≡ z
          right-inverse-of {x} (inj₁ z) with pt (neck-e₂ (ppneck′ x)) ≟ pt e
          right-inverse-of (inj₁ z) | yes p =
                           cong inj₁ (PropEq.proof-irrelevance (pt-inj p) z)
          right-inverse-of (inj₁ z) | no ¬p = ⊥-elim (¬p (cong pt z))
          right-inverse-of {x} (inj₂ y) with pt (neck-e₂ (ppneck′ x)) ≟ pt e
          right-inverse-of (inj₂ y) | yes p = ⊥-elim (y (pt-inj p))
          right-inverse-of (inj₂ y) | no ¬p =
            cong inj₂ (≢-proof-irrelevance (λ x → ¬p (cong pt x)) y)

  bij₁ : ∀ {A : Set} {P : A → Set} → (Σ A (λ x → P x ⊎ ¬ (P x))) ↔
                                     ((Σ A P) ⊎ (Σ A (λ x → ¬ (P x))))
  bij₁ {A} {P} =
    record { to = record { _⟨$⟩_ = to ; cong = cong to } ;
             from = record { _⟨$⟩_ = from ; cong = cong from } ;
             inverse-of = record { left-inverse-of = left-inverse-of ;
                                   right-inverse-of = right-inverse-of }}
    where to : (Σ A (λ x → P x ⊎ ¬ (P x))) → ((Σ A P) ⊎ (Σ A (λ x → ¬ (P x))))
          to (proj₁ , inj₁ x) = inj₁ (proj₁ , x)
          to (proj₁ , inj₂ y) = inj₂ (proj₁ , y)

          from : ((Σ A P) ⊎ (Σ A (λ x → ¬ (P x)))) → 
                            (Σ A (λ x → P x ⊎ ¬ (P x)))
          from (inj₁ x) = (proj₁ x) , (inj₁ (proj₂ x))
          from (inj₂ y) = (proj₁ y) , (inj₂ (proj₂ y))

          left-inverse-of : ∀ x → from (to x) ≡ x
          left-inverse-of (proj₁ , inj₁ x) = refl
          left-inverse-of (proj₁ , inj₂ y) = refl

          right-inverse-of : ∀ x → to (from x) ≡ x
          right-inverse-of (inj₁ x) = refl
          right-inverse-of (inj₂ y) = refl
  
  bij₂ : ∀ {e f q} → (M≢ e f q) ↔
         Σ (F.Fin (suc ⌈ n /2⌉)) (λ x → Σ (M≢ e f q)
                       (λ x₁ → ρ (neck-e₂ (ppneck′ (proj₁ x₁))) f ≡ F.toℕ x))
  bij₂ {e} {f} {q} =
    record { to = record { _⟨$⟩_ = to ; cong = cong to } ;
             from = record { _⟨$⟩_ = from ; cong = cong from } ;
             inverse-of = record { left-inverse-of = left-inverse-of ;
                                   right-inverse-of = right-inverse-of } }
    where open Data.Nat.≤-Reasoning
          helper : ∀ {e₂ f} → ρ e₂ f ≤ ⌈ n /2⌉
          helper {e₂} {f} = begin ρ e₂ f
                                    ≤⟨ A₁'-ρ {e₂} {f} ⟩
                                  ⌊ n /2⌋
                                    ≤⟨ ⌊≤⌉ n ⟩
                                  (⌈ n /2⌉ ∎)
          
          to : (M≢ e f q) →
            Σ (F.Fin (suc ⌈ n /2⌉)) (λ x → Σ (M≢ e f q)
              (λ x₁ → ρ (neck-e₂ (ppneck′ (proj₁ x₁))) f ≡ F.toℕ x))

          to (m , proof) =  (F.fromℕ≤ {ρ (neck-e₂ (ppneck′ m)) f}
                            (s≤s A₁'-ρ-ceil)) , ((m , proof) ,
                                                sym (F.toℕ-fromℕ≤ _)) 
  
          from : Σ (F.Fin (suc ⌈ n /2⌉)) (λ x → Σ (M≢ e f q)
                   (λ x₁ → ρ (neck-e₂
                             (ppneck′ (proj₁ x₁))) f ≡ F.toℕ x)) → (M≢ e f q)
          from (_ , x) = proj₁ x
  
          left-inverse-of : ∀ x → from (to x) ≡ x
          left-inverse-of (m , proof) = refl

          GK : {a b : ℕ} {c : b < a} {d : F.Fin a} → b ≡ F.toℕ d →
                                                     F.fromℕ≤ {b} c ≡ d
          GK {c = c} {d} refl = F.fromℕ≤-toℕ d c
          
          right-inverse-of : ∀ x → to (from x) ≡ x
          right-inverse-of (kk , m , eq) with (GK {c = (s≤s A₁'-ρ-ceil)} eq)
          right-inverse-of (._ , m , eq) | refl =
                               Inverse.to Σ-≡,≡↔≡ ⟨$⟩
                                 (refl , (Inverse.to Σ-≡,≡↔≡ ⟨$⟩
                                   (refl ,
                                     (PropEq.proof-irrelevance _ eq))))          
  bij : ∀ {e f q} → M e f (suc q) ↔
        (M≡ e f q ⊎ Σ (F.Fin (suc ⌈ n /2⌉))
            (λ x → Σ (M≢ e f q)
                     (λ x₁ → ρ (neck-e₂ (ppneck′ (proj₁ x₁))) f ≡ F.toℕ x)))
  bij {e} {f} {q} = Iid ⊎-↔ bij₂ ∘ bij₁ {A = M e f (suc q)}
                        {P = λ x → neck-e₂ (ppneck′ x) ≡ e} ∘
                           bij₀ ∘ Isym bij₋₁

      where open import Relation.Binary.Sum

  m : (r : ℕ) → (q : ℕ) → Σ ℕ (λ x → (e f : P) → (ρ≡r : ρ e f ≡ r) →
                                                      (F.Fin x) ↔ (M e f q))
  m zero zero = 1 , (λ e f ρ≡0 →
    record
      { to = record { _⟨$⟩_ = to {e} {f} {ρ≡0} ; cong = cong to }
      ; from = record { _⟨$⟩_ = from {e} {f} ; cong = cong from }
      ; inverse-of =
        record
          { left-inverse-of = left-inverse-of {e} {f} {ρ≡0}
          ; right-inverse-of = right-inverse-of }})
    where
      to : ∀ {e f} {ρ≡0 : ρ e f ≡ 0} → F.Fin 1 → M e f zero
      to {e} {f} {ρ≡0} F.zero rewrite ρ≡0⇒e≡f ρ≡0 = [ f ] , refl
      to (F.suc ())

      from : ∀ {e f} → M e f zero → F.Fin 1
      from _ = F.zero
  
      left-inverse-of : ∀ {e f} {ρ≡0 : ρ e f ≡ 0} →
                        ∀ x → from {e} {f} (to {e} {f} {ρ≡0} x) ≡ x
      left-inverse-of {e} {f} {ρ≡0} F.zero rewrite ρ≡0⇒e≡f ρ≡0 = refl
      left-inverse-of (F.suc ())

      right-inverse-of : ∀ {e f} {ρ≡0 : ρ e f ≡ 0} →
                         ∀ x → to {e} {f} {ρ≡0} (from {e} {f} x) ≡ x
      right-inverse-of {e} {.e} {ρ≡0 = ρ≡0} ([ .e ] , refl)
        with to {e} {e} {ρ≡0} F.zero
      ... | [ .e ] , refl = refl
      ... | nck ∷ ppc , ()
      right-inverse-of (_ ∷ ppc , ())

  m (suc r) zero = 0 , (λ e f ρ≡r →
    record
    { to = record { _⟨$⟩_ = to ; cong = cong to }
    ; from = record { _⟨$⟩_ = from {e} {f} {ρ≡r} ; cong = cong from }
    ; inverse-of =
       record
         { left-inverse-of = left-inverse-of
         ; right-inverse-of = right-inverse-of }})
    where to : ∀ {e} {f} → F.Fin 0 → M e f 0
          to ()

          from : ∀ {e} {f} {ρ≡sucr : ρ e f ≡ suc r} → M e f 0 → F.Fin 0
          from {ρ≡sucr = pr} ([ e ] , refl) with trans (sym pr) (ρee≡0 {e})
          from ([ e ] , refl) | ()
          from (_ ∷ _ , ())

          left-inverse-of : ∀ {e} {f} {ρ≡sucr : ρ e f ≡ suc r} →
                              ∀ x → from {e} {f} {ρ≡sucr} (to {e} {f} x) ≡ x
          left-inverse-of ()

          right-inverse-of : ∀ {e} {f} {ρ≡sucr : ρ e f ≡ suc r} →
                               ∀ x → to {e} {f} (from {e} {f} {ρ≡sucr} x) ≡ x
          right-inverse-of {ρ≡sucr = pr} ([ e ] , refl)
            with trans (sym pr) (ρee≡0 {e})
          right-inverse-of ([ e ] , refl) | ()
          right-inverse-of (_ ∷ _ , ())
    

  m r (suc q) = ((1 + t) * proj₁ (m r q) +
                sum′ {suc ⌈ n /2⌉} (tabulate
                              (λ x → proj₁ (k r (F.toℕ x)) *
                                     proj₁ (m (F.toℕ x) q)))) ,
                    λ e f ρ≡r → (Isym bij ∘ bij₇ ρ≡r) ∘ bij₆
    where
    bij₆ : F.Fin ((1 + t) * proj₁ (m r q) +
                 sum′ {suc ⌈ n /2⌉} (tabulate
                                    (λ x → proj₁ (k r (F.toℕ x)) *
                                           proj₁ (m (F.toℕ x) q)))) ↔
                 ((F.Fin (1 + t) × F.Fin (proj₁ (m r q))) ⊎
                 Σ (F.Fin (suc ⌈ n /2⌉))
                   (λ x → F.Fin (proj₁ (k r (F.toℕ x))) ×
                          F.Fin (proj₁ (m (F.toℕ x) q))))
    bij₆ = (Isym prod-bij) ⊎-↔
           (SP.↔ Iid (λ {x} →
             Isym (prod-bij {proj₁ (k r (F.toℕ x))}
                            {proj₁ (m (F.toℕ x) q)})) ∘
                  vec-bij _) ∘ Isym sum-bij
        where open import Relation.Binary.Sum

    bij₈ : ∀ {e f} {i : ℕ} →
             Σ (M e f (suc q)) (λ x → (neck-e₂ $ ppneck′ x) ≢ e ×
                                      ρ (neck-e₂ $ ppneck′ x) f ≡ i) ↔
             Σ (Σ (Neck e) (λ nck → (M (neck-e₂ nck) f q)))
                  (λ x → neck-e₂ (proj₁ x) ≢ e × ρ (neck-e₂ (proj₁ x)) f ≡ i) 
    bij₈ {e} {f} {i}= SP.↔
         (record
         { to = record { _⟨$⟩_ = to ; cong = cong to }
         ; from = record { _⟨$⟩_ = from ; cong = cong from }
         ; inverse-of =
           record
           { left-inverse-of = left-inverse-of
           ; right-inverse-of = right-inverse-of }}) Iid
      where to : M e f (suc q) → Σ (Neck e) (λ nck → (M (neck-e₂ nck) f q))
            to x = < ppneck′ , pptail′ > x

            from : Σ (Neck e) (λ nck → (M (neck-e₂ nck) f q)) → M e f (suc q) 
            from x = ppc-app x
            
            left-inverse-of : ∀ x → from (to x) ≡ x
            left-inverse-of = lem-ppc-app

            right-inverse-of : ∀ x → to (from x) ≡ x
            right-inverse-of = lem-pptail′

    bij₉ : ∀ {e f} {i : ℕ} →
           Σ (M e f (suc q)) (λ x → (neck-e₂ $ ppneck′ x) ≢ e ×
                                    ρ (neck-e₂ $ ppneck′ x) f ≡ i) ↔
           Σ (M≢ e f q) (λ x₁ → ρ (neck-e₂ (ppneck′ (proj₁ x₁))) f ≡ i)
    bij₉ =
      record { to = record { _⟨$⟩_ = λ x → ((proj₁ x) ,
                             (proj₁ $ proj₂ x)) ,
                             (proj₂ $ proj₂ x) ; cong = cong _ } ;
               from = record { _⟨$⟩_ = λ x → (proj₁ $ proj₁ x) ,
                                             ((proj₂ $ proj₁ x) , (proj₂ x));
                                             cong = cong _ } ;
               inverse-of = record { left-inverse-of = λ _ → refl ;
                                     right-inverse-of = λ _ → refl } }

    bij₁₀ : ∀ {e f} {i : ℕ} →
            Σ (Σ (Neck e) (λ nck → (M (neck-e₂ nck) f q)))
                             (λ x → neck-e₂ (proj₁ x) ≢ e ×
                                    ρ (neck-e₂ (proj₁ x)) f ≡ i) ↔
            Σ (K e f i) (λ x → M (neck-e₂ $ proj₁ x) f q)
    bij₁₀ =
      record { to = record { _⟨$⟩_ = λ x → ((proj₁ $ proj₁ x) ,
                                           ((proj₁ $ proj₂ x) ,
                                           (proj₂ $ proj₂ x))) ,
                                           (proj₂ $ proj₁ x) ; cong = cong _}
             ; from = record { _⟨$⟩_ = λ x → ((proj₁ $ proj₁ x) ,
                                           (proj₂ x)) ,
                                           (proj₂ $ proj₁ x); cong = cong _ }
             ; inverse-of = record
                            { left-inverse-of = λ _ → refl ;
                              right-inverse-of = λ _ → refl } }
             
    bij₁₁ : ∀ {e} {f} {ρ≡r : ρ e f ≡ r} → {i : ℕ} →
             (F.Fin (proj₁ (k r i)) × F.Fin (proj₁ (m i q))) ↔
              Σ (K e f i) (λ x → M (neck-e₂ $ proj₁ x) f q)
    bij₁₁ {e} {f} {ρ≡r} {i} =
      SP.↔ (proj₂ (k r i) e f ρ≡r)
                  (λ {x} → (proj₂ (m i q) _ _
                     (proj₂ $ proj₂ (Inverse.to
                              (proj₂ (k r i) e f ρ≡r) ⟨$⟩ x))))
        where open Data.Nat.≤-Reasoning 

    bij₁₂ : ∀ {e} {f} →
            M≡ e f q ↔ (L# e × M e f q)
    bij₁₂ = λ {e} {f} →
                record
                { to = record { _⟨$⟩_ = to {e} {f} ; cong = cong to }
                ; from = record { _⟨$⟩_ = from {e} {f} ; cong = cong from }
                ; inverse-of =
                    record
                    { left-inverse-of = left-inverse-of {e} {f}
                    ; right-inverse-of = right-inverse-of {e} {f}
                    }
                }
      where to : ∀ {e f} → M≡ e f q → L# e × M e f q
            to (([ e₁ ] , ()) , proj₃)
            to (((e₁ ∶ e#e₁ , e₂ ∶ e₁#e₂) ∷ ppc , ww) , refl) =
                                          e₁ ∶ e#e₁ , ppc , (cong pred ww)
  
            from : ∀ {e} {f} → L# e × M e f q →  M≡ e f q
            from {e} {f} (x , y) =
              (((x , (e ∶ (#sym (pf x)))) ∷ proj₁ y) ,
                                cong suc (proj₂ y)) , refl

            left-inverse-of : ∀ {e f} → ∀ x → from {e} {f} (to x) ≡ x
            left-inverse-of (([ e₁ ] , ()) , proj₃)
            left-inverse-of (((e₂ ∶ e#e₁ , e₁ ∶ e₁#e₂) ∷ ppc , proj₂) , refl)
                            = Inverse.to Σ-≡,≡↔≡ ⟨$⟩
                              ((Inverse.to Σ-≡,≡↔≡ ⟨$⟩
                                (refl , (PropEq.proof-irrelevance
                                        (cong suc (cong pred proj₂)) proj₂)))
                                      , PropEq.proof-irrelevance _ refl)

            right-inverse-of : ∀ {e f} → ∀ x → to {e} {f} (from x) ≡ x
            right-inverse-of (proj₁ , x) = Inverse.to Σ-≡,≡↔≡ ⟨$⟩
                                           (refl , (Inverse.to Σ-≡,≡↔≡ ⟨$⟩
                                             (refl ,
                                             (PropEq.proof-irrelevance _ _))))

    bij₁₃ : ∀ {e} {f} {ρ≡r : ρ e f ≡ r} →
            (F.Fin (1 + t) × F.Fin (proj₁ (m r q))) ↔ (L# e × M e f q)
    bij₁₃ {e} {f} {ρ≡r} = SP.↔ (Isym (GP-L e)) (proj₂ (m r q) e f ρ≡r)

    bij₇ : ∀ {e f} → ρ e f ≡ r →
           ((F.Fin (1 + t) × F.Fin (proj₁ (m r q))) ⊎
           Σ (F.Fin (suc ⌈ n /2⌉))
             (λ x → F.Fin (proj₁ (k r (F.toℕ x))) ×
                          F.Fin (proj₁ (m (F.toℕ x) q))))
             ↔ (M≡ e f q ⊎ Σ (F.Fin (suc ⌈ n /2⌉))
                   (λ x → Σ (M≢ e f q)
                      (λ x₁ → ρ (neck-e₂ (ppneck′ (proj₁ x₁))) f ≡ F.toℕ x)))

    bij₇ {e} {f} ρ≡r =
         (Isym bij₁₂ ∘ bij₁₃ {e} {f} {ρ≡r}) ⊎-↔
           SP.↔ Iid (λ {x} → (bij₉ {e} {f} {i = F.toℕ x} ∘
                Isym (bij₈ {e} {f} {F.toℕ x}) ∘
                Isym (bij₁₀ {e} {f} {F.toℕ x})) ∘
                bij₁₁ {e} {f} {ρ≡r} {i = F.toℕ x})
      where open import Relation.Binary.Sum
