open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import Relation.Binary.PropositionalEquality as PropEq hiding (proof-irrelevance)

open import Data.Bool
open import Data.Bool.Properties

open import Data.Empty

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

  -- Shortest ppchain
  sppc : (e f : P) → ppchain e f
  sppc e f = (sc (pt e) (pt f)) as-ppc  

  -- ρ' is ρ for any ppchain
  ρ' : ∀ {e f} (ppc : ppchain e f) → ℕ
  ρ' {.f} {f} [ .f ] = zero
  ρ' {e} (_∶⟨_⟩∶_ .e e₁ ppc {{e#e₁}} {{e₁#e₂}}) = suc (ρ' ppc)

  -- len ≡ 2 * ρ
  lem-ρ-len : ∀ {e f} {ppc : ppchain e f} → len (ppc as-c) ≡ 2 * ρ' ppc
  lem-ρ-len {.f} {f} {[ .f ]} = refl
  lem-ρ-len {e} {f} {_∶⟨_⟩∶_ .e e₁ ppc {{e#e₁}} {{e₁#e₂}}} rewrite lem-ρ-len {ppc = ppc} = solve 1
                                                                                             (λ x →
                                                                                                con 2 :+ x :+ (x :+ con 0) :=
                                                                                                con 1 :+ x :+ (con 1 :+ (x :+ con 0)))
                                                                                             refl (ρ' ppc)

  -- ρ between any two points
  ρ : (e f : P) → ℕ
  ρ e f = ρ' (sppc e f)

  -- 2 * ρ ≡ lambda
  lem-ρ-lambda : ∀ {e f} → lambda (pt e) (pt f) ≡ 2 * ρ e f
  lem-ρ-lambda {e} {f} with lem-ρ-len {ppc = (sppc e f)}
  ... | a rewrite lem-id₀ {c = sc (pt e) (pt f)} = a

