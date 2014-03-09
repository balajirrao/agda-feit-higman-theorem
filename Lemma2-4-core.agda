open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import Relation.Binary.PropositionalEquality as PropEq hiding (proof-irrelevance)

open import Data.Bool
open import Data.Bool.Properties

open import Data.Empty
open import Data.Unit hiding (_≤?_; _≤_)

open import Data.Product

open import Data.Nat
open import Function

open import Data.Nat.Properties
open SemiringSolver

open import Misc

module Lemma2-4-core where

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
 
  Neck : P → Set
  Neck e = Σ (L# e) (P# Function.∘ Subset.elem)

  neck-e₂ : ∀ {e} → Neck e → P
  neck-e₂ nck = Subset.elem (proj₂ nck)
  
  neck-e₁ : ∀ {e} → Neck e → L
  neck-e₁ nck = Subset.elem (proj₁ nck) 

  .neck-e#e₁ : ∀ {e} → (nck : Neck e) → True ((pt e) #? (ln (neck-e₁ nck)))
  neck-e#e₁ nck =  Subset.proof (proj₁ nck)

  .neck-e₁#e₂ : ∀ {e} → (nck : Neck e) → True ((ln (neck-e₁ nck)) #? (pt (neck-e₂ nck)))
  neck-e₁#e₂ nck =  Subset.proof (proj₂ nck)
       
  lem-ρ'≥ρ : ∀ {e f} {ppc : ppchain e f} →  True (1 ≤? ρ e f) → True (1 ≤? ρ' ppc)
  lem-ρ'≥ρ {e} {f} {ppc} ≥1 = fromWitness
                                (begin
                                 1 ≤⟨ toWitness ≥1 ⟩ ρ e f ≤⟨ sppc-ρ-shorter-than ppc ⟩ (ρ' ppc ∎))
    where open Data.Nat.≤-Reasoning

  ppneck : ∀ {e f} (ppc : ppchain e f) → {≥1 : True (1 ≤? ρ' ppc)} → Neck e
  ppneck [ e ] {()}
  ppneck (_∶⟨_⟩∶_  {e₂} e e₁ ppc {{e#e₁}} {{e₁#e₂}}) =  (e₁ , e#e₁) , (e₂ , e₁#e₂)
  
  -- ppneck that can be used with cong. Having an argument ≥1
  -- that depends on the chain ppc makes it not possible to use with cong
  ppneck-gen : ∀ {e f} (ppc : ppchain e f) → {≥1 : True (1 ≤? ρ e f)} → Neck e
  ppneck-gen {e} {f} ppc {≥1} = ppneck ppc
                                {fromWitness
                                  (begin
                                    1 ≤⟨ toWitness ≥1 ⟩
                                    ρ e f
                                      ≤⟨ sppc-ρ-shorter-than ppc ⟩
                                    (ρ' ppc ∎))}
             where open Data.Nat.≤-Reasoning

  tailpp : ∀ {e f} → (ppc : ppchain e f) → {≥1 : True (1 ≤? ρ' ppc)} → ppchain (neck-e₂ (ppneck ppc)) f
  tailpp {.f} {f} [ .f ] {()}
  tailpp (_∶⟨_⟩∶_ _ _ ppc) = ppc

  lem-tailpp-ρ : ∀ {e f} {ppc : ppchain e f} {≥1 : True (1 ≤? ρ' ppc)} → ρ' (tailpp ppc) ≡ pred (ρ' ppc)
  lem-tailpp-ρ {.f} {f} {[ .f ]} {()}
  lem-tailpp-ρ {e} {f} {_∶⟨_⟩∶_ .e e₁ ppc {{e#e₁}} {{e₁#e₂}}} = refl


  module ρ-shortest  where
    lem-neckp : {e f : P} {ppc : ppchain e f} {≥1 : True (1 ≤? ρ' ppc)} → pt (neck-e₂ (ppneck ppc)) ≡ 
                  neck (tail (ppc as-c))
                      
    lem-neckp {.f} {f} {[ .f ]} {()}
    lem-neckp {e} {f} {_∶⟨_⟩∶_ .e e₁ ppc {{e#e₁}} {{e₁#e₂}}} = refl

    lem-tailpp : ∀ {e f} {ppc : ppchain e f} {≥1 : True (1 ≤? ρ' ppc)} →
                         len ((tailpp ppc) as-c) ≡ len (tail (tail (ppc as-c)))
    lem-tailpp {.f} {f} {[ .f ]} {()}
    lem-tailpp {e} {f} {_∶⟨_⟩∶_ .e e₁ ppc {{e#e₁}} {{e₁#e₂}}} = refl

    tailpp-ρ-shortest : ∀ {e f} {ppc : ppchain e f} → {≥1 : True (1 ≤? ρ' ppc)} →
                          ppc is-ρ-shortest → tailpp ppc is-ρ-shortest
    tailpp-ρ-shortest {e} {f} {ppc = ppc} {≥1} cis =
                          helper₂ ( begin (
                                    2 * ρ' (tailpp ppc)
                                      ≡⟨ sym lem-2xρ-len ⟩ 
                                    len (tailpp ppc as-c) 
                                      ≡⟨ lem-tailpp {ppc = ppc} ⟩
                                    len (tail (tail (ppc as-c)))
                                      ≡⟨ tail-shortest
                                         (tail-shortest {c = ppc as-c} helper) ⟩
                                    len (sc (neck (tail (ppc as-c)) ) (pt f))
                                      ≡⟨ helper₁ ⟩
                                    len (sc (pt (neck-e₂ (ppneck ppc))) (pt f))
                                      ≡⟨ lem-2xρ-lambda ⟩ 2 * ρ (neck-e₂ (ppneck ppc)) f ∎)
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

            helper₁ : len (sc (neck (tail (ppc as-c))) (pt f)) ≡
                                          len (sc (pt (neck-e₂ (ppneck ppc))) (pt f))
            helper₁ rewrite sym (lem-neckp {ppc = ppc} {≥1}) = refl

            helper₂ : ∀ {x y} → 2 * x ≡ 2 * y → x ≡ y
            helper₂ {x} {y} p = cancel-*-right x y (
                                begin
                                  x * 2
                                    ≡⟨ solve 1 (λ a → a :* con 2 := con 2 :* a) refl x ⟩
                                  2 * x ≡⟨ p ⟩ 2 * y
                                    ≡⟨ solve 1 (λ a → con 2 :* a := a :* con 2) refl y ⟩
                                  (y * 2 ∎))
  open ρ-shortest public using (tailpp-ρ-shortest)

  sppc-irred : ∀ {e f} → irred (sppc e f as-c)
  sppc-irred {e} {f} rewrite lem-id₀ {c = sc (pt e) (pt f)} = shortest-irred (sc (pt e) (pt f)) refl

  ρ≡0⇒e≡f : ∀ {e f} → ρ e f ≡ 0 → e ≡ f
  ρ≡0⇒e≡f {e} {f} eq with sppc e f
  ρ≡0⇒e≡f eq | [ e ] = refl
  ρ≡0⇒e≡f () | _∶⟨_⟩∶_ e e₁ c {{e#e₁}} {{e₁#e₂}}

  ρee≡0 : ∀ {e} → ρ e e ≡ 0
  ρee≡0 {e} = helper (sppc-ρ-shorter-than [ e ])
    where helper : ∀ {x} → x ≤ 0 → x ≡ 0
          helper z≤n = refl
  
  pt-inj : ∀ {x y} → pt x ≡ pt y → x ≡ y
  pt-inj refl = refl


  ln-inj : ∀ {x y} → ln x ≡ ln y → x ≡ y
  ln-inj refl = refl
