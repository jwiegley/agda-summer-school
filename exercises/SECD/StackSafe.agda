-- An implementation of Landin's SECD machine. Adapted from
-- Danvy 2003 (A Rational Deconstruction of Landin's SECD Machine).
module SECD.StackSafe where

open import Prelude
open import Lists

open import Term
open import Term.Show
open import Term.Parse
open WellTyped

data Value : Type → Set

Env : Cxt → Set
Env Γ = All (λ { (x , a) → Value a }) Γ

data Value where
  lit     : Nat → Value nat
  suc     : Value (nat => nat)
  closure : ∀ {Γ a b} (x : Name) → Env Γ → Term ((x , a) ∷ Γ) b → Value (a => b)

data Directive Γ : ? → ? → Set where
  term  : ∀ {Δ a b} → (t : Term Γ a) → Directive Γ (t ∷ a ∷ Δ) (b ∷ Δ)
  apply : ∀ {Δ a b} → Directive Γ (a => b ∷ a ∷ Δ) (b ∷ Δ)

StackType = ?

Stack : StackType → Set
Stack Δ = All Value Δ

Control : Cxt → StackType → StackType → Set
Control Γ Δ θ = Path (Directive Γ) Δ θ

record Snapshot θ a : Set where
  constructor snapshot
  field
    {Δ}         : StackType
    stack       : Stack Δ
    {Γ}         : Cxt
    environment : Env Γ
    control     : Control Γ (θ ++ Δ) (a ∷ [])

Dump : Type → Type → Set
Dump = Path (λ a b → Snapshot (a ∷ []) b)

record SECD a b : Set where
  constructor secd
  field
    current : Snapshot [] b
    dump    : Dump b a

  open Snapshot current public

infix 1 _∣_∣_∣_
pattern _∣_∣_∣_ s e c d = secd (snapshot s e c) d

data StepResult a : Set where
  done  : Value a → StepResult a
  next  : ∀ {b} → SECD a b → StepResult a
  error : String → StepResult a

step : ∀ {a b} → SECD a b → StepResult a

step (v ∷ [] ∣ _ ∣ [] ∣ []) = done v

step (v ∷ [] ∣ e′ ∣ [] ∣ (snapshot s e c) ∷ d) =
  next (v ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term (lit n) ∷ c ∣ d) =
  next (lit n ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term (var x) ∷ c ∣ d) =
  case lookup e x of
  λ { nothing  → error ("variable out of scope: " & x)
    ; (just v) → next (v ∷ s ∣ e ∣ c ∣ d) }

step (s ∣ e ∣ term suc ∷ c ∣ d) =
  next (suc ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term (lam x a t) ∷ c ∣ d) =
  next (closure x e t ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ term (app t₁ t₂) ∷ c ∣ d) =
  next (s ∣ e ∣ term t₂ ∷ term t₁ ∷ apply ∷ c ∣ d)

step (suc ∷ lit n ∷ s ∣ e ∣ apply ∷ c ∣ d) =
  next (lit (suc n) ∷ s ∣ e ∣ c ∣ d)

step (closure x e′ t ∷ v ∷ s ∣ e ∣ apply ∷ c ∣ d) =
  next ([] ∣ (x , v) ∷ e′ ∣ term t ∷ [] ∣ (snapshot s e c) ∷ d)

step ([]                      ∣ _ ∣ []        ∣ _) = error "empty stack on return"
step (_ ∷ _ ∷ _               ∣ _ ∣ []        ∣ _) = error "more than one stack element on return"
step ([]                      ∣ _ ∣ apply ∷ _ ∣ _) = error "apply on empty stack"
step (_ ∷ []                  ∣ _ ∣ apply ∷ _ ∣ _) = error "apply on singleton stack"
step (lit _ ∷ _ ∷ _           ∣ _ ∣ apply ∷ _ ∣ _) = error "apply literal"
step (suc ∷ suc ∷ _           ∣ _ ∣ apply ∷ _ ∣ _) = error "apply suc to suc"
step (suc ∷ closure _ _ _ ∷ _ ∣ _ ∣ apply ∷ _ ∣ _) = error "apply suc to closure"

{-# NO_TERMINATION_CHECK #-}
run′ : ∀ {a} → SECD a → Value a
run′ s with step s
... | next s′ = run′ s′
... | done v  = right v
... | error e = left e 

run : Term → Either String Value
run t = run′ ([] ∣ [] ∣ term t ∷ [] ∣ [])

-- Show instance for values --

private
  showValue : Nat → Value → ShowS
  showEnv   : Env → ShowS

  showValue p (lit n)         = shows n
  showValue p suc             = showString "suc"
  showValue p (closure x e v) = showParen (p > 0) $ showEnv e ∘ showString (" λ " & x & " → ") ∘ shows v

  showBinding : Name × Value → ShowS
  showBinding (x , v) = showString x ∘ showString " = " ∘ showValue 0 v

  showEnv′ : Env → ShowS
  showEnv′ []      = showString ""
  showEnv′ [ b ]   = showBinding b
  showEnv′ (b ∷ e) = showBinding b ∘ showString ", " ∘ showEnv′ e

  showEnv e = showString "[" ∘ showEnv′ e ∘ showString "]"

ShowValue : Show Value
ShowValue = record { showsPrec = showValue }
