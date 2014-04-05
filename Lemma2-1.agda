open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties
open Data.Nat.≤-Reasoning

open import Data.Product
open import Data.Empty
open import Data.Unit hiding (_≤_; _≤?_; setoid; _≟_)

open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import Relation.Binary

open import Data.Bool hiding (_≟_)

open import Relation.Binary.PropositionalEquality as PropEq

open import Function.Equality as FunEq

open import Function.Inverse hiding (sym)

open import Function.Related.TypeIsomorphisms

open import Data.Fin using (Fin)
open import Misc
open SemiringSolver

module Lemma2-1 where
  open import GenPolygon public
  
  T#sym : ∀ {x y} → True (x #? y) → True (y #? x)
  T#sym p = fromWitness (#sym (toWitness p))

  T≢sym : ∀ {x y} → False (x ≟ y) → False (y ≟ x)
  T≢sym p = fromWitnessFalse (λ x → toWitnessFalse p (sym x))

  lem-pp : ∀ {x y} {c : chain (pt x) (pt y)} → Even (len c) 
  lem-lp : ∀ {x y} {c : chain (ln x) (pt y)} → Odd (len c) 

  lem-pp {c = [ ._ ]} = evenZero
  lem-pp {c = _∷_ ._ {{e<>f}} {{e#f}} c} with head c
  lem-pp {x₁} {y} {_∷_ .(pt x₁) {{e<>f}} {{e#f}} c} | pt x = ⊥-elim (IP-pt e<>f e#f)
  lem-pp {x₁} {y} {_∷_ .(pt x₁) c} | ln x = oddEven lem-lp

  lem-lp {c = _∷_ ._ {{e<>f}} {{e#f}} c} with head c
  lem-lp {x₁} {y} {_∷_ .(ln x₁) c} | pt x = evenOdd lem-pp
  lem-lp {x₁} {y} {_∷_ .(ln x₁) {{e<>f}} {{e#f}} c} | ln x = ⊥-elim (IP-ln e<>f e#f)

  rev : ∀ {x y} (c : chain x y) → chain y x
  rev {.y} {y} [ .y ] = [ y ]
  rev {x} (_∷_ .x {{x<>y}} {{x#y}} c) = rev c ++ (_∷_ (head c) 
                  {{T≢sym x<>y}}
                  {{T#sym x#y}} [ x ])

  lem-rev-len : ∀ {x y} {c : chain x y} → len (rev c) ≡ len (c)
  lem-rev-len {c = [ ._ ]} = refl
  lem-rev-len {x} {y} {c = _∷_ ._ {{e<>f}} {{e#f}} c} rewrite lem-++-len {c = rev c} {c' = (_∷_ (head c) 
                  {{T≢sym e<>f}}
                  {{T#sym e#f}} [ x ])} | lem-rev-len {c = c} = solve 1 (λ z → z :+ con 1 := con 1 :+ z) refl (len c)
  lem-pl : ∀ {x y} {c : chain (pt x) (ln y)} → Odd (len c) 
  lem-ll : ∀ {x y} {c : chain (ln x) (ln y)} → Even (len c)
  
  lem-pl {c = _∷_ ._ {{e<>f}} {{e#f}} c} with head c
  lem-pl {x₁} {y} {_∷_ .(pt x₁) {{e<>f}} {{e#f}} c} | pt x = ⊥-elim (IP-pt e<>f e#f)
  lem-pl {x₁} {y} {_∷_ .(pt x₁) {{e<>f}} {{e#f}} c} | ln x = evenOdd lem-ll
  
  lem-ll {c = [ ._ ]} = evenZero
  lem-ll {c = _∷_ ._ {{e<>f}} {{e#f}} c} with head c
  lem-ll {x₁} {y} {_∷_ .(ln x₁) {{e<>f}} {{e#f}} c} | pt x = oddEven lem-pl
  lem-ll {x₁} {y} {_∷_ .(ln x₁) {{e<>f}} {{e#f}} c} | ln x = ⊥-elim (IP-ln e<>f e#f)

  module Lemma2-1-pt where
    lem₀ : {e : P} {e₁ : L# e} {f : X}  → Even (lambda (pt e) f) → Odd (lambda (ln (el e₁)) f)
    lem₀ {e₁ = l ∶ #} {pt x} x₁ = lem-lp
    lem₀ {e} {e₁ = l ∶ #} {ln x} x₁ = ⊥-elim (oddEvenEither x₁ lem-pl)

    lem₁ : {e : P} {e₁ : L# e} {f : X}  → Odd (lambda (pt e) f) → Even (lambda (ln (el e₁)) f)
    lem₁ {e₁ = l ∶ #} {pt x} x₁ = ⊥-elim (oddEvenEither lem-pp x₁)
    lem₁ {e₁ = l ∶ #} {ln x} x₁ = lem-ll

    lem₂ : {e : P} {e₁ : L# e} {f : X} → lambda (pt e) f ≡ n → lambda (ln (el e₁)) f ≢ n
    lem₂ {e} {e₁} {f} λ≡n eq with parity (lambda (pt e) f)
    ... | isEven p = oddEvenEither (subst Even (trans λ≡n (sym eq)) p) (lem₀ {e} {e₁} p)
    ... | isOdd p = oddEvenEither (lem₁ {e} {e₁} p)  (subst Odd (trans λ≡n (sym eq)) p)

    lem₃ : {e : P} {e₁ : L# e} {f : X} → lambda (pt e) f ≡ n → lambda (ln (el e₁)) f < n
    lem₃ {e} {e₁} {f} λ≡n = ≤-≢⇒< (A₁' {ln (el e₁)} {f}) (lem₂ {e} {e₁} λ≡n)

    lem₄ : {e : P} {e₁ : L# e} {f : X} → lambda (pt e) f ≡ n → lambda (ln (el e₁)) f ≮ (pred (n)) 
    lem₄ {e} {e₁} {f} λ≡n p with sc-is-shorter-than (_∷_ (pt e) {{fromWitnessFalse (λ ())}} {{(pf e₁)}} (sc (ln (el e₁)) f))
    ... | z with nn | begin n ≡⟨ sym λ≡n ⟩ lambda (pt e) f ≤⟨ z ⟩ _ ≤⟨ p ⟩ ( pred (n)) ∎
    ... | y | k = helper k
        where open Data.Nat.≤-Reasoning
              helper : ∀ {k} → suc k ≤ k → ⊥
              helper (s≤s t) = helper (t)

    lem₅ : {e : P} {e₁ : L# e} {f : X} → lambda (pt e) f ≡ n → lambda (ln (el e₁)) f ≡ (pred (n))
    lem₅ {e} {e₁} {f} eq = ≤-≥⇒≡ (pred-mono (lem₃ {e} {e₁} eq)) (≰⇒> (λ x → lem₄ {e} {e₁} eq (s≤s x)))

    F : (e : P) (f : X) → Σ (chain (pt e) f) (λ c → len c ≡ n) → L# e
    F _ ._ ([ ._ ] , ())
    F _ _ (_∷_ ._  {{e<>f}} {{e#f}} c , len≡n) with head c
    F e f₁ (_∷_ .(pt e) {{e<>f}} {{e#f}} c , len≡n) | pt x = ⊥-elim (IP-pt e<>f e#f)
    F e f₁ (_∷_ .(pt e) {{e<>f}} {{e#f}} c , len≡n) | ln x = x ∶ e#f

    F⁻¹ : (e : P) (f : X) → lambda (pt e) f ≡ n →  L# e → Σ (chain (pt e) f) (λ c → len c ≡ n) 
    F⁻¹ e f λ≡n (l ∶ #)  = _∷_ (pt e) {{fromWitnessFalse (λ ())}} (sc (ln l) f) , PropEq.cong suc (lem₅ {e₁ = l ∶ #} λ≡n)

    lem-id : (e : P) (f : X) → (λ≡n : lambda (pt e) f ≡ n) → (x : Σ (chain (pt e) f) (λ c → len c ≡ n)) → (F⁻¹ e f λ≡n (F e f x)) ≡ x
    lem-id e .(pt e) λ≡n ([ .(pt e) ] , ())
    lem-id e f λ≡n (_∷_ .(pt e) {{e<>f}} {{e#f}} c , proof) with (head c)
    lem-id e f₁ λ≡n (_∷_ .(pt e) {{e<>f}} {{e#f}} c , proof) | pt x = ⊥-elim (IP-pt e<>f e#f)
    lem-id e f λ≡n (_∷_ .(pt e) {{e<>f}} {{e#f}} c , proof) | ln x with PropEq.cong (el) (A₂ ((sc (ln x) f) ∶ (≡⇒≤ (PropEq.cong suc (lem₅ {e} {x ∶ (e#f)} λ≡n)) , shortest-irred _ refl)) (c ∶ ((≡⇒≤ proof) , shortest-irred c (tail-shortest {c = (pt e) ∷ c} (trans proof (sym λ≡n))))))
    lem-id e f₁ λ≡n (_∷_ .(pt e) {{e<>f}} {{e#f}} .(sc (ln x) f₁) , proof) | ln x | refl = Inverse.to Σ-≡,≡↔≡ ⟨$⟩ (refl , (proof-irrelevance _ proof))

    I : (e : P) (f : X) → lambda (pt e) f ≡ n → (Σ (chain (pt e) f) (λ c → len c ≡ n)) ↔ (L# e)
    I e f λ≡n = record { to = record { _⟨$⟩_ = F e f; cong = PropEq.cong (F e f) };
                     from = record { _⟨$⟩_ = F⁻¹ e f λ≡n ; cong = PropEq.cong (F⁻¹ e f λ≡n) } ;
                     inverse-of = record {
                                  left-inverse-of = lem-id e f λ≡n;
                                  right-inverse-of = λ x → refl } }
  open Lemma2-1-pt public using (I)

  module Lemma2-1-ln where
    lem₀ : {e : L} {e₁ : P# e} {f : X}  → Even (lambda (ln e) f) → Odd (lambda (pt (el e₁)) f)
    lem₀ {e₁ = l ∶ #} {ln x} x₁ = lem-pl
    lem₀ {e} {e₁ = l ∶ #} {pt x} x₁ = ⊥-elim (oddEvenEither x₁ lem-lp)

    lem₁ : {e : L} {e₁ : P# e} {f : X}  → Odd (lambda (ln e) f) → Even (lambda (pt (el e₁)) f)
    lem₁ {e₁ = l ∶ #} {ln x} x₁ = ⊥-elim (oddEvenEither lem-ll x₁)
    lem₁ {e₁ = l ∶ #} {pt x} x₁ = lem-pp

    lem₂ : {e : L} {e₁ : P# e} {f : X} → lambda (ln e) f ≡ n → lambda (pt (el e₁)) f ≡ n → ⊥
    lem₂ {e} {e₁} {f} λ≡n eq with parity (lambda (ln e) f)
    ... | isEven p = oddEvenEither (subst Even (trans λ≡n (sym eq)) p) (lem₀ {e} {e₁} p)
    ... | isOdd p = oddEvenEither (lem₁ {e} {e₁} p)  (subst Odd (trans λ≡n (sym eq)) p)

    lem₃ : {e : L} {e₁ : P# e} {f : X} → lambda (ln e) f ≡ n → lambda (pt (el e₁)) f < n
    lem₃ {e} {e₁} {f} λ≡n = ≤-≢⇒< (A₁' {pt (el e₁)} {f}) (lem₂ {e} {e₁} λ≡n)

    lem₄ : {e : L} {e₁ : P# e} {f : X} → lambda (ln e) f ≡ n → lambda (pt (el e₁)) f < (pred (n)) → ⊥
    lem₄ {e} {e₁} {f} λ≡n p with sc-is-shorter-than (_∷_ (ln e) {{fromWitnessFalse (λ ())}} {{(pf e₁)}} (sc (pt (el e₁)) f))
    ... | z with nn | begin n ≡⟨ sym λ≡n ⟩ lambda (ln e) f ≤⟨ z ⟩ _ ≤⟨ p ⟩ ( pred (n)) ∎
    ... | y | k = helper k
        where open Data.Nat.≤-Reasoning
              helper : ∀ {k} → suc k ≤ k → ⊥
              helper (s≤s t) = helper (t)

    lem₅ : {e : L} {e₁ : P# e} {f : X} → lambda (ln e) f ≡ n → lambda (pt (el e₁)) f ≡ (pred (n))
    lem₅ {e} {e₁} {f} eq = ≤-≥⇒≡ (pred-mono (lem₃ {e} {e₁} eq)) (≰⇒> (λ x → lem₄ {e} {e₁} eq (s≤s x)))

    F : (e : L) (f : X) → Σ (chain (ln e) f) (λ c → len c ≡ n) → P# e
    F _ ._ ([ ._ ] , ())
    F _ _ (_∷_ ._  {{e<>f}} {{e#f}} c , len≡n) with head c
    F e f₁ (_∷_ .(pt e) {{e<>f}} {{e#f}} c , len≡n) | ln x = ⊥-elim (IP-ln e<>f e#f)
    F e f₁ (_∷_ .(pt e) {{e<>f}} {{e#f}} c , len≡n) | pt x = x ∶ e#f

    F⁻¹ : (e : L) (f : X) → lambda (ln e) f ≡ n →  P# e → Σ (chain (ln e) f) (λ c → len c ≡ n) 
    F⁻¹ e f λ≡n (l ∶ #)  = _∷_ (ln e) {{fromWitnessFalse (λ ())}} (sc (pt l) f) , PropEq.cong suc (lem₅ {e₁ = l ∶ #} λ≡n)

    lem-id : (e : L) (f : X) → (λ≡n : lambda (ln e) f ≡ n) → (x : Σ (chain (ln e) f) (λ c → len c ≡ n)) → (F⁻¹ e f λ≡n (F e f x)) ≡ x
    lem-id e .(ln e) λ≡n ([ .(ln e) ] , ())
    lem-id e f λ≡n (_∷_ .(ln e) {{e<>f}} {{e#f}} c , proof) with (head c)
    lem-id e f₁ λ≡n (_∷_ .(ln e) {{e<>f}} {{e#f}} c , proof) | ln x = ⊥-elim (IP-ln e<>f e#f)
    lem-id e f₁ λ≡n (_∷_ .(ln e) {{e<>f}} {{e#f}} c , proof) | pt x with PropEq.cong (el) (A₂ ((sc (pt x) f₁) ∶ ( ≡⇒≤ (PropEq.cong suc (lem₅ {e} {x ∶ (e#f)} λ≡n)) , shortest-irred _ refl)) (c ∶ ((≡⇒≤ proof) , shortest-irred c  (tail-shortest {c = ln e ∷ c} (trans proof (sym λ≡n))))))
    lem-id e f₁ λ≡n (_∷_ .(pt e) {{e<>f}} {{e#f}} .(sc (pt x) f₁) , proof) | pt x | refl = Inverse.to Σ-≡,≡↔≡ ⟨$⟩ (refl , (proof-irrelevance _ proof))

    J : (e : L) (f : X) → lambda (ln e) f ≡ n → Inverse (PropEq.setoid (Σ (chain (ln e) f) (λ c → len c ≡ n))) (PropEq.setoid (P# e))
    J e f λ≡n = record { to = record { _⟨$⟩_ = F e f; cong = PropEq.cong (F e f) };
                     from = record { _⟨$⟩_ = F⁻¹ e f λ≡n ; cong = PropEq.cong (F⁻¹ e f λ≡n) } ;
                     inverse-of = record {
                                  left-inverse-of = lem-id e f λ≡n;
                                  right-inverse-of = λ x → refl } }

  open Lemma2-1-ln public using (J)
