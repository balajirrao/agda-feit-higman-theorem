\begin{document}
\begin{code}
open import Data.Nat
open import Data.Nat.Properties

open import Data.Fin using (Fin)

open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Product

open import Relation.Binary.PropositionalEquality as PropEq
--open PropEq.≡-Reasoning 

open import Relation.Nullary.Core

open import Function.Equality hiding (setoid; cong; _∘_)
open import Function.Inverse renaming (sym to Isym)

open import Misc

open import GenPolygon

open SemiringSolver


module Lemma2-2 where

  open import Lemma2-1 public

  postulate
    GP : (e : X) → Σ X (λ f → lambda e f ≡ n)

  step0 : (e : P) → Odd n → L
  step0 e on with (GP (pt e))
  step0 e on | pt x , proj₂ = ⊥-elim (oddEvenEither lem-pp (subst Odd (sym proj₂) on))
  step0 e on | ln x , proj₂ = x

  rev′ : ∀ {x y} → (chain x y) → (chain y x)
  rev′ [ e ] = [ e ]
  rev′ (_∷_ {f} e {{e<>f}} {{e#f}} c) = rev′ c ++ _∷_ f {{≢sym e<>f}} {{#sym e#f}} [ e ]

  lem-rev′-len : ∀ {x y} {c : chain x y} → len (rev′ c) ≡ len (c)
  lem-rev′-len {c = [ ._ ]} = refl
  lem-rev′-len {x} {y} {c = _∷_ {f} ._ {{e<>f}} {{e#f}} c} =
                   trans (lem-++-len {c = rev′ c}
                     {_∷_ f {{≢sym e<>f}} {{#sym e#f}} [ x ]})
                            (trans (+-comm {len (rev′ c)} {1})
                                   (cong suc (lem-rev′-len {c = c})))
           
  rev : ∀ {x y k} → Σ (chain x y) (λ c → len c ≡ k) → Σ (chain y x) (λ c → len c ≡ k)
  rev (c , p) = (rev′ c) , trans (lem-rev′-len {c = c}) p

  lem-++-empty : ∀ {e f} → (c : chain e f) → c ++ [ f ] ≡ c
  lem-++-empty [ e ] = refl
  lem-++-empty (_∷_ {f} e {{e<>f}} {{e#f}} c) rewrite lem-++-empty c = refl

  ++-assoc : ∀ {e f g h} → (c : chain e f) (c′ : chain f g) (c″ : chain g h) → c ++ c′ ++ c″ ≡ c ++ (c′ ++ c″)
  ++-assoc [ e ] b c = refl
  ++-assoc (_∷_ e {{e<>f}} {{e#f}} a) b c rewrite ++-assoc a b c = refl

  rev-++ : ∀ {e f g} (c : chain e f) (c' : chain f g) → rev′ (c ++ c') ≡ rev′ c' ++ rev′ c
  rev-++ [ e ] c' = sym (lem-++-empty (rev′ c'))
  rev-++ (_∷_ {f₁} e {{e<>f}} {{e#f}} c) c' rewrite rev-++ c c' =
                              ++-assoc (rev′ c') (rev′ c) (_∷_ f₁ {{≢sym e<>f}} {{#sym e#f}} [ e ])

  rev²-id : ∀ {e f} → (c : chain e f) → (rev′ (rev′ c)) ≡ c
  rev²-id [ e ] = refl
  rev²-id (_∷_ {f₁} e {{e<>f}} {{e#f}} c)
          rewrite rev-++ (rev′ c) (_∷_ f₁ {{≢sym e<>f}} {{#sym e#f}} [ e ]) |
                                                                     rev²-id c = refl

  rev↔ : ∀ {e f k} → (Σ (chain e f) (λ c → len c ≡ k)) ↔ (Σ (chain f e) (λ c → len c ≡ k))
  rev↔ = Σ↔ (record { to = record { _⟨$⟩_ = rev′ ; cong = cong _ } ;
                      from = record { _⟨$⟩_ = rev′ ; cong = cong _ } ;
                      inverse-of = record { left-inverse-of = rev²-id ;
                      right-inverse-of = rev²-id } })
            (record { to = record { _⟨$⟩_ = λ x → trans lem-rev′-len x ;
                      cong = cong _ } ;
                      from = record { _⟨$⟩_ = λ x → trans (sym lem-rev′-len) x ;
                      cong = cong _ } })
    where postulate Σ↔ : predicate-irrelevant-Σ↔


  λef≤λfe : ∀ {e f} → lambda f e ≤ lambda e f
  λef≤λfe {e} {f} = begin
                    lambda f e
                      ≤⟨ sc-is-shorter-than rev′ (sc e f) ⟩
                    len (rev′ (sc e f))
                      ≡⟨ lem-rev′-len ⟩
                    len (sc e f)
                      ≡⟨ sc-shortest ⟩
                    (lambda e f ∎)
    where open Data.Nat.≤-Reasoning
  
  λfe≤λef :  ∀ {e f} → lambda e f ≤ lambda f e
  λfe≤λef {e} {f} = begin
                    lambda e f
                      ≤⟨ sc-is-shorter-than rev′ (sc f e) ⟩
                    len (rev′ (sc f e))
                      ≡⟨ lem-rev′-len ⟩
                    len (sc f e)
                      ≡⟨ sc-shortest ⟩
                    (lambda f e ∎)
    where open Data.Nat.≤-Reasoning
  
  λfe≡λef :  ∀ {e f} → lambda e f ≡ lambda f e
  λfe≡λef = ≤-≥⇒≡ λef≤λfe λfe≤λef 

  lemma-2-2 : ∀ {e f} → (lambda (pt e) (ln f) ≡ n) →
                        Inverse (setoid (L# e)) (setoid (P# f))
  lemma-2-2 {e} {f} p = J f (pt e)
                        (trans λfe≡λef p) ∘ rev↔ ∘ Isym (I e (ln f) p)
\end{code}
\end{document}
