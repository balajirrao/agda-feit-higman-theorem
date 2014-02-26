open import Relation.Nullary.Decidable
open import Relation.Nullary.Core

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq

open import Data.Product hiding (map)
open import Data.Empty
open import Data.Unit hiding (_≟_; _≤?_)

open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties
open Data.Nat.≤-Reasoning

open SemiringSolver

open import Data.Bool hiding (_≟_)

import Level

module IncidenceGeometry where

  -- Set of points and lines
  postulate
    P L : Set

  -- The set O consists of both points and lines
  data O : Set where
    pt : P → O
    ln : L → O

  
  postulate
    _#_ : Rel O Level.zero      -- The incidence relation #

    _#?_ : Decidable _#_        -- We assume decidability of incidence relation. We later use
                                -- an incident matrix anyway

    _≟_ : Decidable {A = O} _≡_ -- We assume decidablity of equality of objects of O
                                -- for the same reason
    
    #sym : ∀ {e f} → e # f → f # e -- # is symetric
    #refl : ∀ {e} → e # e          -- # is reflexive

  infixr 5 _∷_   
  data chain : O → O → Set where
    [_] : (e : O) → chain e e
    _∷_ : ∀ {f g} (e : O) {{e<>f : False (e ≟ f)}} {{e#f : True (e #? f)}} (c : chain f g) → chain e g    

  len : ∀ {e f} (c : chain e f) → ℕ
  len [ _ ] = zero
  len (_ ∷ c) = suc (len c)

  head : ∀ {e f} (c : chain e f) → O
  head {e} _ = e

  second :  ∀ {e f} (c : chain e f) → {{≥1 : True (1 ≤? len c)}} → O
  second {.f} {f} [ .f ] {{()}}
  second (_ ∷ c) {{_}} = head c

  tail : ∀ {e f} (c : chain e f) → {{≥1 : True (1 ≤? len c)}} → chain (second c) f
  tail {.f} {f} [ .f ] {{()}}
  tail {e} (.e ∷ c) {{_}} = c
  
  infixl 5 _++_   
  _++_ : ∀ {e f g} → (c : chain e f) → (c' : chain f g) → chain e g
  [ e ] ++ c = c
  (e ∷ c) ++ c' = e ∷ (c ++ c')

  lem-++-len : ∀ {e f g} → {c : chain e f} → {c' : chain f g} → len (c ++ c') ≡ len c + len c'
  lem-++-len {.f} {f} {g} {[ .f ]} = refl
  lem-++-len {e} {f} {g} {_∷_ .e {{e<>f}} {{e#f}} c} {c'} rewrite lem-++-len {c = c} {c' = c'} = refl

  record Segment {e f : O} (c : chain e f) : Set where
    constructor segment
    field
      e₀ : O
      e₁ : O
      e₂ : O
      chain-prev : chain e e₀
      chain-next : chain e₂ f
      {{e₀#e₁}} : True (e₀ #? e₁)
      {{e₁#e₂}} : True (e₁ #? e₂)
      {{e₀≢e₁}} : False (e₀ ≟ e₁)
      {{e₁≢e₂}} : False (e₁ ≟ e₂)
      {{total-chain}} : c ≡ chain-prev ++ (e₀ ∷ e₁ ∷ chain-next)

  segment-⊂ : ∀ {e f g} {{e<>f : False (e ≟ f)}} {{e#f : True (e #? f)}} → 
                {c : chain f g} → Segment c → Segment (e ∷ c)
  segment-⊂ {e} {f} {g} {c = c} s = record {
                                      e₀ = Segment.e₀ s;
                                      e₁ = Segment.e₁ s;
                                      e₂ = Segment.e₂ s;
                                      chain-prev = e ∷ Segment.chain-prev s;
                                      chain-next = Segment.chain-next s;
                                      e₀#e₁ = Segment.e₀#e₁ s;
                                      e₁#e₂ = Segment.e₁#e₂ s;
                                      e₀≢e₁ = Segment.e₀≢e₁ s;
                                      e₁≢e₂ = Segment.e₁≢e₂ s;
                                      total-chain = cong (_∷_ e) (Segment.total-chain s)}

 
  _th-segment-of_ : ∀ {e f} (n : ℕ) (c : chain e f) → {{≥2 : True (2 ≤? len c)}} {{≤len : True (n ≤? pred (pred (len c)))}} → Segment c
  _th-segment-of_ {.f} {f} n [ .f ] {{()}} {{≤len}}
  _th-segment-of_ {e} {f} n (_∷_ .e {{e<>f}} {{e#f}} [ .f ]) {{()}} {{≤len}}
  _th-segment-of_ zero (e ∷ f ∷ [ g ]) {{tt}} {{tt}} = record { e₀ = e; e₁ = f; e₂ = g; chain-prev = [ e ]; chain-next = [ g ] }
  _th-segment-of_ {e} {f} (suc n) (_∷_ {f₁} .e {{e<>f}} {{e#f}} (_∷_ .f₁ {{e<>f₁}} {{e#f₁}} [ .f ])) {{tt}} {{()}}
  _th-segment-of_ zero (e ∷ f ∷ g ∷ c) {{≥2}} {{≤len}} = record { e₀ = e; e₁ = f; e₂ = g; chain-prev = [ e ]; chain-next = g ∷ c }
  _th-segment-of_ (suc n) (_ ∷ f ∷ g ∷ c) {{≥2}} {{≤len}} = segment-⊂ (_th-segment-of_ n (f ∷ g ∷ c) {{tt}} {{fromWitness (pred-mono (toWitness ≤len))}})


  reducible : ∀ {e f} {c : chain e f} → Segment c → Set
  reducible s = True (Segment.e₀ s #? Segment.e₂ s)

  short-circuit : ∀ {e f} {c : chain e f} (s : Segment c) → reducible s → ∃ (λ (c' : chain e f) → len c' < len c)
  short-circuit (segment e₀ e₁ e₂ c c' {{total-chain = tc}}) r rewrite tc | lem-++-len {c = c} {c' = e₀ ∷ e₁ ∷ c'} with e₀ ≟ e₂
  short-circuit (segment .e₂ e₁ e₂ c c') r | yes refl = (c ++ c') ,
                                                        (begin
                                                         suc (len (c ++ c'))
                                                            ≡⟨ cong suc (lem-++-len {c = c} {c' = c'}) ⟩
                                                          suc (len c + len c')
                                                            ≤⟨ ≤-steps 1 (n≤m+n zero (suc (len c + len c'))) ⟩
                                                          suc (suc (len c + len c'))
                                                            ≡⟨ solve 2
                                                               (λ x y → con 2 :+ x :+ y := x :+ (con 1 :+ con 1 :+ y))
                                                                    refl (len c) (len c') ⟩
                                                          len c + suc (suc (len c')) ∎)
  ... | no ¬p = (c ++ _∷_ e₀ {{fromWitnessFalse ¬p}} {{r}} c') ,
                                                           (begin suc (len(c ++ _∷_ e₀ {{fromWitnessFalse ¬p}} {{r}} c'))
                                                             ≡⟨ cong suc (lem-++-len {c = c} {c' = _∷_ e₀ {{fromWitnessFalse ¬p}} {{r}} c'}) ⟩
                                                           suc (len c + suc (len c')) ≡⟨ solve 2
                                                               (λ x y → con 1 :+ x :+ (con 1 :+ y) := x :+ (con 1 :+ con 1 :+ y))
                                                                 refl (len c) (len c') ⟩
                                                           len c + suc (suc (len c')) ∎)

  irred : ∀ {e f} (c : chain e f) → {{≥2 : True (2 ≤? len c)}} → Set
  irred {.f} {f} [ .f ] {{()}}
  irred {e} {f} (_∷_ .e {{e<>f}} {{e#f}} [ .f ]) {{()}}
  irred (e ∷ f ∷ c) {{≥2}} = {n : _} {{≤len : True (n ≤? len c)}} →
                               reducible (_th-segment-of_ n (e ∷ f ∷ c) {{tt}} ) → ⊥



