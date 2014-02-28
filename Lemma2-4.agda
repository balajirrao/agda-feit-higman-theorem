open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import Relation.Binary.PropositionalEquality as PropEq hiding (proof-irrelevance)

open import Data.Bool
open import Data.Bool.Properties

open import Data.Empty
open import Data.Unit hiding (_≤?_; _≤_)

open import Data.Nat

open import Data.Nat.Properties
open SemiringSolver

open import Misc

module Lemma2-4 where

  open import GenPolygon public

  data ppchain : P → P → Set where
    [_] : (e : P) → ppchain e e
    _∶⟨_⟩∶_ : ∀ {e₂ f} (e : P) → (e₁ : L) → (c : ppchain e₂ f) →
                     .{{e#e₁ : True(pt e #? ln e₁)}} .{{e₁#e₂ : True (ln e₁ #? pt e₂)}} → ppchain e f
 
  -- View a chain as a ppchain
  _as-ppc : ∀ {e f} (c : chain (pt e) (pt f)) → ppchain e f
  _as-ppc {.f} {f} [ .(pt f) ] = [ f ]
  _as-ppc {e} {f} (_∷_ .(pt e) {{e<>f}} {{e#f}} [ .(pt f) ]) = ⊥-elim (IP-pt e<>f e#f)
  _as-ppc {e} (_∷_ {f₁} .(pt e) {{e<>f}} {{e#f}} (_∷_ {e₁} .f₁ {{e<>f₁}} {{e#f₁}} c)) with e₁ | f₁
  _as-ppc {e} (_∷_ {f} .(pt e) {{e<>f}} {{e#f}} (_∷_ .f {{e<>f₁}} {{e#f₁}} c)) | pt x | pt x₁ = ⊥-elim (IP-pt e<>f e#f)
  _as-ppc {e} (_∷_ {f} .(pt e) {{e<>f}} {{e#f}} (_∷_ .f {{e<>f₁}} {{e#f₁}} c)) | ln x | pt x₁ = ⊥-elim (IP-pt e<>f e#f)
  _as-ppc {e} (_∷_ {f} .(pt e) {{e<>f}} {{e#f}} (_∷_ .f {{e<>f₁}} {{e#f₁}} c)) | ln x | ln x₁ = ⊥-elim (IP-ln e<>f₁ e#f₁)
  _as-ppc {e} (_∷_ {f} .(pt e) {{e<>f}} {{e#f}} (_∷_ .f {{e<>f₁}} {{e#f₁}} c)) | pt x | ln x₁ = e ∶⟨ x₁ ⟩∶ (c as-ppc)

  -- View a ppchain as a chain
  _as-c : ∀ {e f} (ppc : ppchain e f) → chain (pt e) (pt f)
  _as-c {.f} {f} [ .f ] = [ pt f ]
  _as-c {e} (_∶⟨_⟩∶_ .e e₁ ppc {{e#e₁}} {{e₁#e₂}}) = _∷_ (pt e)
                                                         {{fromWitnessFalse (λ ())}}
                                                           (_∷_ (ln e₁)
                                                         {{fromWitnessFalse (λ ())}}
                                                           (ppc as-c))

  -- as-ppc ∘ as-c ≡ id
  lem-id₀ : ∀ {e f} {c : chain (pt e) (pt f)} → (c as-ppc) as-c ≡ c
  lem-id₀ {.f} {f} {[ .(pt f) ]} = refl
  lem-id₀ {e} {f} {_∷_ .(pt e) {{e<>f}} {{e#f}} [ .(pt f) ]} = ⊥-elim (IP-pt e<>f e#f)
  lem-id₀ {e} {f} {_∷_ .(pt e) {{e<>f}} {{e#f}} (_∷_ {e₁} f₁ {{e<>f₁}} {{e#f₁}} c)} with e₁ | f₁
  lem-id₀ {e} {f₂} {_∷_ .(pt e) {{e<>f}} {{e#f}} (_∷_ f {{e<>f₁}} {{e#f₁}} c)} | pt x | pt x₁ = ⊥-elim (IP-pt e<>f e#f)
  lem-id₀ {e} {f₂} {_∷_ .(pt e) {{f}} {{f₁}} (_∷_ e#f {{e<>f₁}} {{e#f₁}} c)} | pt x | ln x₁ rewrite (lem-id₀ {c = c}) = refl
  lem-id₀ {e} {f₂} {_∷_ .(pt e) {{e<>f}} {{e#f}} (_∷_ f {{e<>f₁}} {{e#f₁}} c)} | ln x | pt x₁ = ⊥-elim (IP-pt e<>f e#f)
  lem-id₀ {e} {f₂} {_∷_ .(pt e) {{f}} {{f₁}} (_∷_ e#f {{e<>f₁}} {{e#f₁}} c)} | ln x | ln x₁ = ⊥-elim (IP-ln e<>f₁ e#f₁)

  -- as-c ∘ as-ppc ≡ id
  lem-id₁ : ∀ {e f} {ppc : ppchain e f} → (ppc as-c) as-ppc ≡ ppc
  lem-id₁ {.f} {f} {[ .f ]} = refl
  lem-id₁ {e} {f} {_∶⟨_⟩∶_ .e e₁ ppc {{e#e₁}} {{e₁#e₂}}} rewrite (lem-id₁ {ppc = ppc}) = refl

  -- ρ' is ρ for any ppchain
  ρ' : ∀ {e f} (ppc : ppchain e f) → ℕ
  ρ' {.f} {f} [ .f ] = zero
  ρ' {e} (_∶⟨_⟩∶_ .e e₁ ppc {{e#e₁}} {{e₁#e₂}}) = suc (ρ' ppc)

  -- len ≡ 2 * ρ
  lem-2xρ-len : ∀ {e f} {ppc : ppchain e f} → len (ppc as-c) ≡ 2 * ρ' ppc
  lem-2xρ-len {.f} {f} {[ .f ]} = refl
  lem-2xρ-len {e} {f} {_∶⟨_⟩∶_ .e e₁ ppc {{e#e₁}} {{e₁#e₂}}} rewrite lem-2xρ-len {ppc = ppc} = solve 1
                                                                                             (λ x →
                                                                                                con 2 :+ x :+ (x :+ con 0) :=
                                                                                                con 1 :+ x :+ (con 1 :+ (x :+ con 0)))
                                                                                             refl (ρ' ppc)

  lem-len/2-ρ : ∀ {e f} {ppc : ppchain e f} → ⌊ len (ppc as-c) /2⌋ ≡ ρ' ppc
  lem-len/2-ρ {.f} {f} {[ .f ]} = refl
  lem-len/2-ρ {e} {f} {_∶⟨_⟩∶_ .e e₁ ppc {{e#e₁}} {{e₁#e₂}}} = cong suc lem-len/2-ρ

  -- Shortest ppchain
  sppc : (e f : P) → ppchain e f
  sppc e f = (sc (pt e) (pt f)) as-ppc  

  -- ρ between any two points
  ρ : (e f : P) → ℕ
  ρ e f = ρ' (sppc e f)
  
  -- 2 * ρ ≡ lambda
  lem-2xρ-lambda : ∀ {e f} → lambda (pt e) (pt f) ≡ 2 * ρ e f
  lem-2xρ-lambda {e} {f} with lem-2xρ-len {ppc = (sppc e f)}
  ... | a rewrite lem-id₀ {c = sc (pt e) (pt f)} = a

  lem-lambda/2-ρ : ∀ {e f} → ⌊ lambda (pt e) (pt f) /2⌋ ≡ ρ e f
  lem-lambda/2-ρ {e} {f} with lem-len/2-ρ {ppc = (sppc e f)}
  ... | a rewrite lem-id₀ {c = sc (pt e) (pt f)} = a

  -- sppc is shorter than (in terms of ρ) ..
  sppc-ρ-shorter-than_ : ∀ {e f} (ppc : ppchain e f) → ρ e f ≤ ρ' ppc
  sppc-ρ-shorter-than_ {e} {f} ppc rewrite
                                 sym (lem-lambda/2-ρ {e} {f}) |
                                 sym (lem-len/2-ρ {ppc = ppc})
                                   = ⌊n/2⌋-mono (sc-is-shorter-than (ppc as-c))
  
  -- A given chain is shortest in terms of ρ when ..
  _is-ρ-shortest : ∀ {e f} (ppc : ppchain e f) → Set
  _is-ρ-shortest {e} {f} ppc = ρ' ppc ≡ ρ e f
  
  sppc-is-ρ-shortest : ∀ {e f} → (sppc e f) is-ρ-shortest
  sppc-is-ρ-shortest = refl

  -- neck of a ppchain is a point
  neckp : ∀ {e f} (ppc : ppchain e f) → {{≥1 : True (1 ≤? ρ' ppc)}} → P
  neckp {.f} {f} [ .f ] {{()}}
  neckp {e} (_∶⟨_⟩∶_ {e₂} .e e₁ ppc {{e#e₁}} {{e₁#e₂}}) {{_}} = e₂
  
  tailpp : ∀ {e f} → (ppc : ppchain e f) → {{≥1 : True (1 ≤? ρ' ppc)}} → ppchain (neckp ppc) f
  tailpp {.f} {f} [ .f ] {{()}}
  tailpp (_∶⟨_⟩∶_ _ _ ppc) {{_}} = ppc

  module ρ-shortest  where
    private
      len≥2 : {e f : P} {{ppc : ppchain e f}} {{≥1 : True (1 ≤? ρ' ppc)}} → 2 ≤ (len (ppc as-c))
      len≥2 {{ppc = ppc}} {{≥1}} = begin
             2
               ≤⟨ m≤m {2} *-mono toWitness ≥1 ⟩
             2 * ρ' ppc
               ≡⟨ sym lem-2xρ-len ⟩
             (len (ppc as-c) ∎)
            where open Data.Nat.≤-Reasoning

      len≥1 : {e f : P} {{ppc : ppchain e f}} {{≥1 : True (1 ≤? ρ' ppc)}} → True (1 ≤? (len (ppc as-c)))
      len≥1 {{ppc = ppc}} {{≥1}} = fromWitness (begin
                         1
                           ≤⟨ s≤s z≤n ⟩
                         2 
                           ≤⟨ len≥2 ⟩
                         (len (ppc as-c) ∎))
            where open Data.Nat.≤-Reasoning


      taillen≥1 : {e f : P} {{ppc : ppchain e f}} {{≥1 : True (1 ≤? ρ' ppc)}} → True (1 ≤? (len (tail (ppc as-c) {{len≥1}})))
      taillen≥1 {{ppc = ppc}} {{≥1}} = fromWitness
                                       (begin
                                         1 ≤⟨ pred-mono len≥2 ⟩
                                         pred (len (ppc as-c)) ≡⟨ sym (lem-tail-len {c = ppc as-c} {{len≥1}}) ⟩
                                         (len (tail (ppc as-c) {{len≥1}} ) ∎))
            where open Data.Nat.≤-Reasoning


    lem-neckp : {e f : P} {ppc : ppchain e f} {{≥1 : True (1 ≤? ρ' ppc)}} → pt (neckp ppc) ≡ 
                  neck (tail (ppc as-c) {{len≥1}}) {{taillen≥1}}
                      
    lem-neckp {.f} {f} {[ .f ]} = λ {{}}
    lem-neckp {e} {f} {_∶⟨_⟩∶_ .e e₁ ppc {{e#e₁}} {{e₁#e₂}}} = refl

    lem-tailpp : ∀ {e f} {ppc : ppchain e f} {{≥1 : True (1 ≤? ρ' ppc)}} →
                         len ((tailpp ppc) as-c) ≡ len (tail (tail (ppc as-c) {{len≥1}}) {{taillen≥1}})
    lem-tailpp {.f} {f} {[ .f ]} = λ {{}}
    lem-tailpp {e} {f} {_∶⟨_⟩∶_ .e e₁ ppc {{e#e₁}} {{e₁#e₂}}} = refl

    tailpp-ρ-shortest : ∀ {e f} {ppc : ppchain e f} {{≥1 : True (1 ≤? ρ' ppc)}} →
                          ppc is-ρ-shortest → tailpp ppc is-ρ-shortest
    tailpp-ρ-shortest {e} {f} {ppc = ppc} {{≥1}} cis =
                          helper₂ ( begin (
                                    2 * ρ' (tailpp ppc)
                                      ≡⟨ sym lem-2xρ-len ⟩ 
                                    len (tailpp ppc as-c) 
                                      ≡⟨ lem-tailpp {ppc = ppc} ⟩
                                    len (tail (tail (ppc as-c) {{len≥1}}) {{taillen≥1}})
                                      ≡⟨ tail-shortest {{taillen≥1}}
                                         (tail-shortest {c = ppc as-c} {{len≥1}} helper) ⟩
                                    len (sc (neck (tail (ppc as-c) {{len≥1}}) {{taillen≥1}}) (pt f))
                                      ≡⟨ helper₁ ⟩
                                    len (sc (pt (neckp ppc )) (pt f))
                                      ≡⟨ lem-2xρ-lambda ⟩ 2 * ρ (neckp ppc) f ∎)
                                  )
      where open ≡-Reasoning
            helper : len (ppc as-c) ≡ len (sc (pt e) (pt f))
            helper =  begin
                      len (ppc as-c)
                        ≡⟨ lem-2xρ-len ⟩
                      2 * ρ' ppc
                        ≡⟨ cong (_*_ 2) cis ⟩
                      2 * ρ' (sc (pt e) (pt f) as-ppc) 
                        ≡⟨ sym lem-2xρ-lambda ⟩
                      (len (sc (pt e) (pt f)) ∎)

            helper₁ : len (sc (neck (tail (ppc as-c) {{len≥1}}) {{taillen≥1}}) (pt f)) ≡
                                          len (sc (pt (neckp ppc)) (pt f))
            helper₁ rewrite lem-neckp {ppc = ppc} {{≥1}} = refl

            helper₂ : ∀ {x y} → 2 * x ≡ 2 * y → x ≡ y
            helper₂ {x} {y} p = cancel-*-right x y (
                                begin
                                  x * 2
                                    ≡⟨ solve 1 (λ a → a :* con 2 := con 2 :* a) refl x ⟩
                                  2 * x ≡⟨ p ⟩ 2 * y
                                    ≡⟨ solve 1 (λ a → con 2 :* a := a :* con 2) refl y ⟩
                                  (y * 2 ∎))
  open ρ-shortest public using (tailpp-ρ-shortest)
