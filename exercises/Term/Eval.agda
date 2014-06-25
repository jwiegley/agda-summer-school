
module Term.Eval where

open import Prelude

open import Lists
open import Term
open WellTyped

El : Type → Set
El nat      = Nat
El (a => b) = El a → El b

Env : Cxt → Set
Env Γ = All (El ∘ snd) Γ

-- Exercise: Implement an evaluator for well-typed terms.
eval : ∀ {Γ a} → Term Γ a → Env Γ → El a
eval (var _ i) e = lookup∈ e i
eval (app t t₁) e = (eval t e) (eval t₁ e)
eval (lam x a t) e = λ y → eval t (y ∷ e)
eval (lit n) _ = n
eval suc _ = suc

test : Nat
test = eval (app (lam "x" nat (app suc (var "x" (zero refl)))) (lit 10)) []
