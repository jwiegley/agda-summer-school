
module TypeCheck where

open import Prelude
open import Lists

open import Term
open WellTyped
open Unchecked  renaming (Term to Expr)
open import Term.Show
open import Term.Parse

TypeError = String

TC : Set → Set
TC = Either TypeError

typeError : ∀ {A} → TypeError → TC A
typeError = left

data TypeChecked Γ : Expr → Set where
  ok : ∀ a (v : Term Γ a) → TypeChecked Γ (forgetTypes v)

data CheckedVar (Γ : Cxt) x : Set where
  ok : ∀ a (i : (x , a) ∈ Γ) → CheckedVar Γ x

lookupVar : (Γ : Cxt) (x : Name) → TC (Σ Type λ a → (x , a) ∈ Γ)
lookupVar [] x = typeError ("Variable out of scope: " & x)
lookupVar ((y , a) ∷ Γ) x with x == y
lookupVar ((y , a) ∷ Γ) .y | yes refl = return (a , zero refl)
lookupVar ((y , a) ∷ Γ) x  | no _     = fmap (second suc) (lookupVar Γ x)

checkVar : ∀ {Γ x} → Σ Type (λ a → (x , a) ∈ Γ) → TypeChecked Γ (var x)
checkVar (a , i) = ok a (var _ i)

checkLam : ∀ {Γ x a e} → TypeChecked ((x , a) ∷ Γ) e → TypeChecked Γ (lam x a e)
checkLam (ok b v) = ok (_ => b) (lam _ _ v)

checkApp : ∀ {Γ e e₁} → TypeChecked Γ e → TypeChecked Γ e₁
         → TC (TypeChecked Γ (app e e₁))
checkApp (ok nat v) (ok a₁ v₁) = typeError ("nat is not a fun: " & show v)
checkApp (ok (a => b) v) (ok a₁ v₁) with a == a₁
checkApp (ok (a => b) v) (ok .a v₁) | yes refl = right (ok b (app v v₁))
checkApp (ok (a => b) v) (ok a₁ v₁) | no _     = typeError "argument mismatch"

-- Exercise: Implement the type checker. When you are done,
--           go to Lambda.agda and make it type check the
--           input and print the inferred type.
typeCheck : ∀ Γ (e : Expr) → TC (TypeChecked Γ e)
typeCheck Γ (var x) = fmap checkVar (lookupVar Γ x)
typeCheck Γ (lit x) = return (ok nat (lit x))
typeCheck Γ suc = return (ok (nat => nat) suc)
typeCheck Γ (app e e₁) =
    typeCheck Γ e  >>= λ e′  →
    typeCheck Γ e₁ >>= λ e₁′ → checkApp e′ e₁′
typeCheck Γ (lam x f e) = fmap checkLam (typeCheck ((x , f) ∷ Γ) e)

-- Forget which unchecked term we started with.
forgetOrigin : ∀ {Γ e} → TypeChecked Γ e → Σ Type (Term Γ)
forgetOrigin (ok a v) = a , v

parseAndTypeCheck : String → TC (Σ Type (Term []))
parseAndTypeCheck s =
  flip (maybe (typeError "Parse error")) (parseTerm s) $ λ e →
  forgetOrigin <$> typeCheck [] e
