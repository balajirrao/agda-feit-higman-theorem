import Relation.Nullary.Decidable as Dec
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

  -- The set X consists of both points and lines
  data X : Set where
    pt : P → X
    ln : L → X
  
  postulate
    _#_ : Rel X Level.zero
    _#?_ : Decidable _#_ 
    _≟_ : Decidable {A = X} _≡_ 
    #sym : ∀ {e f} → e # f → f # e
    #refl : ∀ {e} → e # e
 
  infixr 5 _∷_   
  data chain : X → X → Set where
    [_] : (e : X) → chain e e
    _∷_ : ∀ {f g} (e : X) .{{e<>f : e ≢ f}}
           .{{e#f : e # f}} (c : chain f g) → chain e g    

  -- length of chains
  len : ∀ {e f} (c : chain e f) → ℕ
  len [ _ ] = zero
  len (_ ∷ c) = suc (len c)

  -- left most element
  head : ∀ {e f} (c : chain e f) → X
  head {e} _ = e

  -- second element form the left
  neck :  ∀ {e f} (c : chain e f) → X
  neck {.f} {f} [ .f ] = f
  neck (_ ∷ c) = head c

  -- behead the chain
  tail : ∀ {e f} (c : chain e f) → chain (neck c) f
  tail {.f} {f} [ .f ] = [ f ]
  tail {e} (.e ∷ c) = c
  
  -- Join two chains
  -- The chains have to end and begin at a common point respectively.
  -- This is done because the len becomes addtive
  infixl 5 _++_   
  _++_ : ∀ {e f g} → (c : chain e f) → (c' : chain f g) → chain e g
  [ e ] ++ c = c
  (e ∷ c) ++ c' = e ∷ (c ++ c')

  -- len is additive
  lem-++-len : ∀ {e f g} → {c : chain e f} → {c' : chain f g} →
                 len (c ++ c') ≡ len c + len c'
  lem-++-len {.f} {f} {g} {[ .f ]} = refl
  lem-++-len {e} {f} {g} {.e ∷ c} {c'} rewrite lem-++-len {c = c} {c' = c'} = refl

  -- A segment is a triple of elements of X such that they form a chain of length 2
  -- A segment is identified as belonging to a particular chain
  record Segment {e f : X} (c : chain e f) : Set where
    constructor segment
    field
      e₀ : X
      e₁ : X
      e₂ : X
      chain-prev : chain e e₀     -- The chain upto the point e₀
      chain-next : chain e₂ f     -- The chain beyond the point e₂
      .{{e₀#e₁}} : e₀ # e₁
      .{{e₁#e₂}} : e₁ # e₂
      .{{e₀≢e₁}} : e₀ ≢ e₁
      .{{e₁≢e₂}} : e₁ ≢ e₂
      {{total-chain}} : c ≡ chain-prev ++ (e₀ ∷ e₁ ∷ chain-next)
      
  -- A segment of a subchain is a segment of a superchain
  segment-⊂ : ∀ {e f g} .{{e<>f : e ≢ f}} .{{e#f : e # f}} → 
                {c : chain f g} → Segment c → Segment (e ∷ c)
  segment-⊂ {e} {c = c} s = record {
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

  -- Get the nth segment of a chain.
  _th-segment-of_ : ∀ {e f} (n : ℕ) (c : chain e f) →
                      {≥2 : Dec.True (2 ≤? len c)}
                      {≤len : Dec.True (n ≤? pred (pred (len c)))} → Segment c
  _th-segment-of_ n [ f ] {()}
  _th-segment-of_ _ (_∷_ ._ [ ._ ]) {()}
  zero th-segment-of (e ∷ f ∷ [ g ]) =
       record { e₀ = e; e₁ = f; e₂ = g; chain-prev = [ e ];
                                        chain-next = [ g ] }
  _th-segment-of_ (suc n) (_∷_ _ (_∷_ ._ [ ._ ])) {_} {()}
  zero th-segment-of (e ∷ f ∷ g ∷ c) =
       record { e₀ = e; e₁ = f; e₂ = g; chain-prev = [ e ];
                                        chain-next = g ∷ c }
  _th-segment-of_ (suc n) (_ ∷ f ∷ g ∷ c) {≥2} {≤len} =
    segment-⊂ (_th-segment-of_ n (f ∷ g ∷ c) {_}
              {Dec.fromWitness (pred-mono (Dec.toWitness ≤len))})

  -- reducible predicate for segments
  reducible : ∀ {e f} {c : chain e f} → Segment c → Set
  reducible s = Segment.e₀ s # Segment.e₂ s

  -- If a chain has a reducible segment, construct a strictly smaller chain 
  -- between the same end points
  short-circuit : ∀ {e f} {c : chain e f} (s : Segment c) →
                    reducible s → ∃ (λ (c' : chain e f) → len c' < len c)
  short-circuit (segment e₀ e₁ e₂ c c' {{total-chain = tc}}) r rewrite tc
                         | lem-++-len {c = c} {c' = e₀ ∷ e₁ ∷ c'} with e₀ ≟ e₂ 
  short-circuit (segment .e₂ e₁ e₂ c c') r | yes refl =
                (c ++ c') ,
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
  ... | no ¬p = (c ++ _∷_ e₀ {{¬p}} {{r}} c') ,
        (begin
           suc (len(c ++ _∷_ e₀ {{¬p}} {{r}} c'))
             ≡⟨ cong suc (lem-++-len {c = c} {c' = _∷_ e₀ {{ ¬p}} {{r}} c'}) ⟩
           suc (len c + suc (len c')) ≡⟨ solve 2
             (λ x y → con 1 :+ x :+ (con 1 :+ y) := x :+ (con 1 :+ con 1 :+ y))
               refl (len c) (len c') ⟩
           len c + suc (suc (len c')) ∎)

  -- irred predicate for chains
  irred : ∀ {e f} (c : chain e f) → Set
  irred {.f} {f} [ .f ] = ⊤
  irred {e} {f} (_∷_ .e {{e<>f}} {{e#f}} [ .f ]) = ⊤
  irred (e ∷ f ∷ c) = {n : _} {≤len : Dec.True (n ≤? len c)} →
                 reducible (_th-segment-of_ n (e ∷ f ∷ c) {≤len = ≤len} ) → ⊥

  irred-∷ : ∀ {y z} (x : X) (c : chain y z) → {≥2 : Dec.True (2 ≤? len c)} →
                      .{x<>y : x ≢ y} → .{x#y : x # y} →
                      (¬x#z : x # (neck c) → ⊥) → irred c → irred (x ∷ c)
  irred-∷ _ [ e₃ ] {≥2 = ()} _ _
  irred-∷ _ (_∷_ e₃ [ ._ ]) {≥2 = ()} _ _
  irred-∷ x (e₃ ∷ z ∷ c) ¬x#z ic = λ {m} {≤len} x₁ → helper {m} {≤len} x₁
    where helper : {k : ℕ} → {≤len : Dec.True (k ≤? (suc (len c)))} →
                 reducible (_th-segment-of_ k (x ∷ e₃ ∷ z ∷ c) {_} {≤len}) → ⊥
          helper {zero} x₁ = ¬x#z (x₁)
          helper {suc k} {≤len} x₁ = ic {k}
                         {Dec.fromWitness (pred-mono (Dec.toWitness ≤len))} x₁

