open import Prelude

data Type : Set where
  nat : Type
  bool : Type

Ctxt = List Type

infix 3 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  zero : ∀ {xs} → x ∈ x ∷ xs
  suc  : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

data Expr (Γ : Ctxt) : Type → Set where
  var   : {X : Type} (x : X ∈ Γ) → Expr Γ X
  lit   : (n : Nat) → Expr Γ nat
  true  : Expr Γ bool
  false : Expr Γ bool
  less  : (a b : Expr Γ nat) → Expr Γ bool
  plus  : (a b : Expr Γ nat) → Expr Γ nat
  if    : {t : Type} (a : Expr Γ bool) (b c : Expr Γ t) → Expr Γ t

Value : Type → Set
Value nat = Nat
Value bool = Bool

data All {A : Set} (P : A → Set) : List A → Set where
  [] : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

lookup∈ : ∀ {A} {P : A → Set} {x xs} → All P xs → x ∈ xs → P x
lookup∈ (p ∷ ps) zero = p
lookup∈ (p ∷ ps) (suc i) = lookup∈ ps i

Env : Ctxt → Set
Env Γ = All Value Γ

eval : ∀ {Γ t} → Env Γ → Expr Γ t → Value t
eval env (var x)       = lookup∈ env x
eval env (lit n)       = n
eval env true          = true
eval env false         = false
eval env (less t t₁)   = eval env t < eval env t₁
eval env (plus t t₁)   = eval env t + eval env t₁
eval env (if t₁ t₂ t₃) = if eval env t₁ then eval env t₂ else eval env t₃

Γ : Ctxt
Γ = nat ∷ bool ∷ []

env : Env Γ
env = 5 ∷ false ∷ []

e : Expr Γ nat
e = if (var (suc zero)) (var zero) (plus (lit 4) (var zero))

-- data Expr : Set where
--   lit   : (n : Nat) → Expr
--   true  : Expr
--   false : Expr
--   less  : (a b : Expr) → Expr
--   plus  : (a b : Expr) → Expr
--   if    : (a b c : Expr) → Expr

-- data Value : Set where
--   nat  : Nat → Value
--   bool : Bool → Value

-- getNat : Value → Maybe Nat
-- getNat (nat x) = just x
-- getNat (bool x) = nothing

-- getBool : Value → Maybe Bool
-- getBool (nat x) = nothing
-- getBool (bool x) = just x

-- eval : Expr → Maybe Value
-- eval (lit n) = just (nat n)
-- eval true = just (bool true)
-- eval false = just (bool false)
-- eval (less e e₁) = (λ n m → bool (n < m)) <$> (getNat =<< eval e)
--                                           <*> (getNat =<< eval e₁)
-- eval (plus e e₁) = eval e₁
-- eval (if e e₁ e₂) = eval e₂
