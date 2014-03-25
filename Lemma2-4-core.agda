open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import Relation.Binary.PropositionalEquality as PropEq hiding (proof-irrelevance)

open import Data.Bool
open import Data.Bool.Properties

open import Data.Empty
open import Data.Unit hiding (_≤?_; _≤_)

open import Data.Product

open import Data.Sum

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
  Neck e = Σ (L# e) (λ x → P# (el x))

  neck-e₂ : ∀ {e} → Neck e → P
  neck-e₂ nck = el (proj₂ nck)
  
  neck-e₁ : ∀ {e} → Neck e → L
  neck-e₁ nck = el (proj₁ nck) 

  .neck-e#e₁ : ∀ {e} → (nck : Neck e) → True ((pt e) #? (ln (neck-e₁ nck)))
  neck-e#e₁ nck =  pf (proj₁ nck)

  .neck-e₁#e₂ : ∀ {e} → (nck : Neck e) → True ((ln (neck-e₁ nck)) #? (pt (neck-e₂ nck)))
  neck-e₁#e₂ nck =  pf (proj₂ nck)
       
  lem-ρ'≥ρ : ∀ {e f} {ppc : ppchain e f} →  True (1 ≤? ρ e f) → True (1 ≤? ρ' ppc)
  lem-ρ'≥ρ {e} {f} {ppc} ≥1 = fromWitness
                                (begin
                                 1 ≤⟨ toWitness ≥1 ⟩ ρ e f ≤⟨ sppc-ρ-shorter-than ppc ⟩ (ρ' ppc ∎))
    where open Data.Nat.≤-Reasoning

  ppneck : ∀ {e f} (ppc : ppchain e f) → {≥1 : True (1 ≤? ρ' ppc)} → Neck e
  ppneck [ e ] {()}
  ppneck (_∶⟨_⟩∶_  {e₂} e e₁ ppc {{e#e₁}} {{e₁#e₂}}) =  (e₁ ∶ e#e₁) , (e₂ ∶ e₁#e₂)

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

  tailpp : ∀ {e f} → (ppc : ppchain e f) → {≥1 : True (1 ≤? ρ' ppc)} → ppchain (neck-e₂ (ppneck  ppc {≥1 = ≥1} )) f
  tailpp {.f} {f} [ .f ] {()}
  tailpp (_∶⟨_⟩∶_ _ _ ppc) = ppc

  lem-tailpp-ρ : ∀ {e f} {ppc : ppchain e f} {≥1 : True (1 ≤? ρ' ppc)} → ρ' (tailpp ppc  {≥1 = ≥1}) ≡ pred (ρ' ppc)
  lem-tailpp-ρ {.f} {f} {[ .f ]} {()}
  lem-tailpp-ρ {e} {f} {_∶⟨_⟩∶_ .e e₁ ppc {{e#e₁}} {{e₁#e₂}}} = refl


  module ρ-shortest  where
    lem-neckp : {e f : P} {ppc : ppchain e f} {≥1 : True (1 ≤? ρ' ppc)} → pt (neck-e₂ (ppneck ppc  {≥1 = ≥1})) ≡ 
                  neck (tail (ppc as-c))
                      
    lem-neckp {.f} {f} {[ .f ]} {()}
    lem-neckp {e} {f} {_∶⟨_⟩∶_ .e e₁ ppc {{e#e₁}} {{e₁#e₂}}} = refl

    lem-tailpp : ∀ {e f} {ppc : ppchain e f} {≥1 : True (1 ≤? ρ' ppc)} →
                         len ((tailpp ppc  {≥1 = ≥1}) as-c) ≡ len (tail (tail (ppc as-c)))
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
  A₂-ρ : ∀ {e f} (ppc ppc' : Σ' (ppchain e f) (λ z → ρ' z < ⌈ n /2⌉ × irred (z as-c))) →
                                                 ppc ≡ ppc'
  A₂-ρ (ppc ∶ p) (ppc' ∶ p') with 
                                  cong (λ x → el x as-ppc) (A₂ (ppc as-c ∶ ( (lem-ρ-len<n (proj₁ p) , proj₂ p)))
                                  (ppc' as-c ∶ ((lem-ρ-len<n (proj₁ p') , proj₂ p'))))
  ... | z rewrite lem-id₁ {ppc = ppc} | lem-id₁ {ppc = ppc'} | z = refl

   
  lem-neckl : {x y : P} {ppc : ppchain x y} {≥1 : True (1 ≤? ρ' ppc)} → ln (neck-e₁ (ppneck ppc)) ≡ 
                      (neck (ppc as-c))
  lem-neckl {ppc = [ e ]} = λ {}
  lem-neckl {ppc = _∶⟨_⟩∶_ ._ _ ppc {{e#e₁}} {{e₁#e₂}}} = refl
 
  T#sym : ∀ {e f} → True (e #? f) → True (f #? e)
  T#sym x = fromWitness (#sym (toWitness x))
   
  neck! : ∀ {e} {nck nck' : Neck e} → e ≢ neck-e₂ nck → neck-e₂ nck ≡ neck-e₂ nck' → nck ≡ nck'
  neck! {e} {e₁ ∶ e#e₁ , e₂ ∶ e₁#e₂} {e₁' ∶ e₁'#e , .e₂ ∶ e₁'#e₂'} neq refl =
                cong (λ x → ppneck-gen x {≥1 = fromWitness ρee₂≥1})
                  (cong el (A₂-ρ ((c as-ppc) ∶ ((s≤s (s≤s z≤n)) , irredc))
                    ((c' as-ppc) ∶ ((s≤s (s≤s z≤n)) , irredc'))))
    where c : chain (pt e) (pt e₂)
          c = _∷_ (pt e) {{fromWitnessFalse (λ ())}} {{e#e₁}} (_∷_ (ln e₁) {{fromWitnessFalse (λ ())}} {{e₁#e₂}} [ pt e₂ ])
  
          c' : chain (pt e) (pt e₂)
          c' =  _∷_ (pt e) {{fromWitnessFalse (λ ())}} {{e₁'#e}} (_∷_ (ln e₁') {{fromWitnessFalse (λ ())}} {{e₁'#e₂'}} [ pt e₂ ])

          irredc : irred c
          irredc {zero} x = IP-pt (fromWitnessFalse (λ eq → neq (pt-inj eq))) x 
          irredc {suc n} {()} x

          irredc' : irred c'
          irredc' {zero} x = IP-pt (fromWitnessFalse (λ eq → neq (pt-inj eq))) x 
          irredc' {suc n} {()} x

          e₁≡e₁' : ln e₁ ≡ ln e₁'
          e₁≡e₁' = cong neck (cong el (A₂ (c ∶ ((s≤s (s≤s (s≤s z≤n))) , irredc)) (c' ∶ ((s≤s (s≤s (s≤s z≤n))) , irredc'))))
   
          result : e₁ ∶ e#e₁ ≡ e₁' ∶ e₁'#e
          result = Σ'≡ {x =  e₁ ∶ e#e₁} {y = e₁' ∶ e₁'#e} (ln-inj e₁≡e₁')

          x≡0or≥1 : ∀ {x} →  (x ≡ 0) ⊎ (x ≥ 1)
          x≡0or≥1 {zero} = inj₁ refl
          x≡0or≥1 {suc x} = inj₂ (s≤s z≤n)

          ρee₂≥1 : ρ e e₂ ≥ 1  
          ρee₂≥1 with x≡0or≥1 {ρ e e₂}
          ρee₂≥1 | inj₁ x = ⊥-elim (neq (ρ≡0⇒e≡f x))
          ρee₂≥1 | inj₂ y = y

  K : (e f : P) (i : ℕ) → Set
  K e f i = Σ (Neck e) (λ nck → (neck-e₂ nck ≢ e) × ρ (neck-e₂ nck) f ≡ i)
