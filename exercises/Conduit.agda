module Conduit where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- data _≡_ {A : Set} : A → A → Set where
--   refl : {x : A} → x ≡ x

-- sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
-- sym {x = x} {y = .x} refl = refl

-- trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- trans {x = x} {y = .x} {z = .x} refl refl = refl

-- subst : ∀ {A B : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
-- subst P refl p = p

-- cong : ∀ {A B : Set} (f : A → B) {x y} → x ≡ y → f x ≡ f y
-- cong f refl = refl

id : ∀ {A : Set} → A → A
id x = x

infixr 9 _∘_
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
_∘_ f g x = f (g x)

infixr 0 _$_
_$_ : ∀ {A B : Set} → (A → B) → A → B
f $ x = f x

const : ∀ {A B : Set} → B → A → B
const x _ = x

record IsFunctor (F : Set → Set)
    (fmap : ∀ {A B} → (A → B) → F A → F B) : Set₁ where
  field
    fun-ident : ∀ {A} → (f : ∀ {B} → B → B) → (x : F A) →
      (∀ {B} {y : B} → f y ≡ y) → fmap f x ≡ x
    fun-compose : ∀ {A B C} (f : A → B) (g : B → C) (x : F A) →
      fmap (g ∘ f) x ≡ (fmap g ∘ fmap f) x

record Functor (F : Set → Set) : Set₁ where
  infixl 4 _<$>_ _<$_
  field
    fmap : ∀ {A B} → (A → B) → F A → F B

    isFunctor : IsFunctor F fmap

  _<$>_ = fmap

  _<$_ : ∀ {A B} → A → F B → F A
  x <$ m = fmap (const x) m

open Functor {{...}} public

record IsApplicative (F : Set → Set)
    (functor : Functor F)
    (pure  : ∀ {A} → A → F A)
    (apply : ∀ {A B} → F (A → B) → F A → F B) : Set₁ where
  field
    app-ident : ∀ {A} (x : F A) → apply (pure id) x ≡ id x
    app-composition : ∀ {X Y Z} (u : F (Y → Z)) (v : F (X → Y)) (w : F X) →
        apply (apply (apply (pure _∘_) u) v) w ≡ apply u (apply v w)
    app-homomorphism : ∀ {X Y} (f : X → Y) (x : X) →
        apply (pure f) (pure x) ≡ pure (f x)
    app-interchange : ∀ {X Y} (u : F (X → Y)) (y : X) →
        apply u (pure y) ≡ apply (pure (λ f → f y)) u

    app-fmap-unit : ∀ {X Y : Set} (f : X → Y) (x : F X) →
        apply (pure f) x ≡ fmap {{functor}} f x

record Applicative (F : Set → Set) : Set₁ where
  infixl 4 _<*>_
  field
    functor : Functor F

    pure : ∀ {A} → A → F A
    apply : ∀ {A B} → F (A → B) → F A → F B

    isApplicative : IsApplicative F functor pure apply

  _<*>_ : ∀ {A B} → F (A → B) → F A → F B
  _<*>_ = apply

open Applicative {{...}} public

record IsMonad (M : Set → Set)
    (functor : Functor M)
    (applicative : Applicative M)
    (join : ∀ {A} → M (M A) → M A) : Set₁ where
  field
    monad-law-1 : ∀ {X} (x : M (M (M X))) →
      join (fmap join x) ≡ join (join x)
    monad-law-2 : ∀ {X} (x : M (M X)) →
      join (fmap pure x) ≡ x
    monad-law-3 : ∀ {X} (x : M X) →
      join (pure x) ≡ x
    monad-law-4 : ∀ {X Y} (f : X -> Y) (x : X) →
      pure (f x) ≡ fmap f (pure x)
    monad-law-5 : ∀ {X Y} (f : X -> Y) (x : M (M X)) →
      join (fmap (fmap f) x) ≡ fmap f (join x)

record Monad (M : Set → Set) : Set₁ where
  infixl 1 _>>=_
  field
    base-functor : Functor M
    applicative : Applicative M

    join : ∀ {A} → M (M A) → M A

    isMonad : IsMonad M base-functor applicative join

  _>>=_ : ∀ {A B} → M A → (A → M B) → M B
  m >>= f = join (fmap f m)

  return : ∀ {A} → A → M A
  return = pure

open Monad {{...}} public

IdentityF : Functor (λ x → x)
IdentityF = record
    { fmap = λ f x → f x

    ; isFunctor = record
        { fun-ident   = λ {A} f x z → z
        ; fun-compose = λ {A} _ _ _ → refl
        }
    }

IdentityA : Applicative (λ x → x)
IdentityA = record
    { functor = IdentityF

    ; pure    = id
    ; apply   = λ f x → f x

    ; isApplicative = record
        { app-ident        = λ {A} x → refl
        ; app-composition  = λ {X} {Y} {Z} v u w → refl
        ; app-homomorphism = λ {X} {Y} x f → refl
        ; app-interchange  = λ {X} {Y} y u → refl

        ; app-fmap-unit    = λ {X} {Y} f x → refl
        }
    }

IdentityM : Monad (λ x → x)
IdentityM = record
    { base-functor = IdentityF
    ; applicative  = IdentityA

    ; join = id

    ; isMonad = record
        { monad-law-1 = λ {X} x → refl
        ; monad-law-2 = λ {X} x → refl
        ; monad-law-3 = λ {X} x → refl
        ; monad-law-4 = λ {X} {Y} f x → refl
        ; monad-law-5 = λ {X} {Y} f x → refl
        }
    }

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just    : ∀ (a : A) → Maybe A

MaybeF : Functor Maybe
MaybeF = record
    { fmap = fmap′

    ; isFunctor = record
        { fun-ident   = fun-ident′
        ; fun-compose = fun-compose′
        }
    }
  where
    fmap′ : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
    fmap′ f Nothing = Nothing
    fmap′ f (Just a) = Just (f a)

    fun-ident′ : ∀ {A} → (f : ∀ {B} → B → B) → (x : Maybe A) →
                   (∀ {B} {y : B} → f y ≡ y) → fmap′ f x ≡ x
    fun-ident′ f Nothing h  = refl
    fun-ident′ f (Just _) h = f (cong Just h)

    fun-compose′
      : ∀ {A B C : Set} (f : A → B) (g : B → C) (x : Maybe A)
      → fmap′ (λ x₁ → g (f x₁)) x ≡ fmap′ g (fmap′ f x)
    fun-compose′ _ _ Nothing  = refl
    fun-compose′ _ _ (Just _) = refl

MaybeA : Applicative Maybe
MaybeA = record
    { functor = MaybeF

    ; pure    = Just
    ; apply   = apply′

    ; isApplicative = record
        { app-ident        = app-ident′
        ; app-composition  = app-composition′
        ; app-homomorphism = λ x f → refl
        ; app-interchange  = app-interchange′

        ; app-fmap-unit    = app-fmap-unit′
        }
    }
  where
    apply′ : ∀ {A B} → Maybe (A → B) → Maybe A → Maybe B
    apply′ Nothing _ = Nothing
    apply′ _ Nothing = Nothing
    apply′ (Just f) (Just x) = Just (f x)

    app-ident′ : ∀ {A} (x : Maybe A) → apply′ (Just id) x ≡ x
    app-ident′ Nothing = refl
    app-ident′ (Just _) = refl

    app-composition′
      : ∀ {X Y Z} (u : Maybe (Y → Z)) (v : Maybe (X → Y)) (w : Maybe X)
      → apply′ (apply′ (apply′ (Just (λ f g x → f (g x))) u) v) w
          ≡ apply′ u (apply′ v w)
    app-composition′ Nothing Nothing Nothing = refl
    app-composition′ Nothing Nothing (Just _) = refl
    app-composition′ Nothing (Just _) Nothing = refl
    app-composition′ Nothing (Just _) (Just _) = refl
    app-composition′ (Just _) Nothing Nothing = refl
    app-composition′ (Just _) Nothing (Just _) = refl
    app-composition′ (Just _) (Just _) Nothing = refl
    app-composition′ (Just _) (Just _) (Just _) = refl

    app-interchange′ : ∀ {X Y} (u : Maybe (X → Y)) (y : X) →
                   apply′ u (Just y) ≡ apply′ (Just (λ f → f y)) u
    app-interchange′ Nothing _ = refl
    app-interchange′ (Just _) _ = refl

    app-fmap-unit′ : ∀ {X Y : Set} (f : X → Y) (x : Maybe X)
                   → apply′ (Just f) x ≡ fmap f x
    app-fmap-unit′ _ Nothing = refl
    app-fmap-unit′ _ (Just _) = refl

MaybeM : Monad Maybe
MaybeM = record
    { base-functor = MaybeF
    ; applicative  = MaybeA

    ; join = join′

    ; isMonad = record
        { monad-law-1 = monad-law-1′
        ; monad-law-2 = monad-law-2′
        ; monad-law-3 = monad-law-3′
        ; monad-law-4 = λ f x → refl
        ; monad-law-5 = monad-law-5′
        }
    }
  where
    join′ : ∀ {A} → Maybe (Maybe A) → Maybe A
    join′ Nothing        = Nothing
    join′ (Just Nothing) = Nothing
    join′ (Just a)       = a

    monad-law-1′ : ∀ {X} (x : Maybe (Maybe (Maybe X))) →
      join′ (fmap {{MaybeF}} join′ x) ≡ join′ (join′ x)
    monad-law-1′ Nothing = refl
    monad-law-1′ (Just Nothing) = refl
    monad-law-1′ (Just (Just Nothing)) = refl
    monad-law-1′ (Just (Just (Just _))) = refl

    monad-law-2′ : ∀ {X} (x : Maybe (Maybe X)) →
      join′ (fmap {{MaybeF}} Just x) ≡ x
    monad-law-2′ Nothing = refl
    monad-law-2′ (Just Nothing) = refl
    monad-law-2′ (Just (Just _)) = refl

    monad-law-3′ : ∀ {X} (x : Maybe X) → join′ (Just x) ≡ x
    monad-law-3′ Nothing = refl
    monad-law-3′ (Just _) = refl

    monad-law-5′ : ∀ {X Y} (f : X → Y) (x : Maybe (Maybe X)) →
      join′ (fmap {{MaybeF}} (fmap {{MaybeF}} f) x) ≡ fmap f (join′ x)
    monad-law-5′ f Nothing = refl
    monad-law-5′ f (Just Nothing) = refl
    monad-law-5′ f (Just (Just _)) = refl

data Either (E A : Set) : Set where
  Left  : ∀ (e : E) → Either E A
  Right : ∀ (a : A) → Either E A

EitherF : ∀ {E : Set} → Functor (Either E)
EitherF {E} = record
    { fmap = fmap′

    ; isFunctor = record
        { fun-ident   = fun-ident′
        ; fun-compose = fun-compose′
        }
    }
  where
    fmap′ : ∀ {A B : Set} → (A → B) → Either E A → Either E B
    fmap′ f (Left e)  = Left e
    fmap′ f (Right a) = Right (f a)

    fun-ident′ : ∀ {A} → (f : ∀ {B} → B → B) → (x : Either E A) →
                   (∀ {B} {y : B} → f y ≡ y) → fmap′ f x ≡ x
    fun-ident′ f (Left _)  h = refl
    fun-ident′ f (Right _) h = f (cong Right h)

    fun-compose′ : ∀ {A B C : Set} (f : A → B) (g : B → C) (x : Either E A)
               → (fmap′ (λ x₁ → g (f x₁))) x ≡ fmap′ g ((fmap′ f) x)
    fun-compose′ _ _ (Left _)  = refl
    fun-compose′ _ _ (Right _) = refl

EitherA : ∀ {E : Set} → Applicative (Either E)
EitherA = record
    { functor = EitherF

    ; pure    = Right
    ; apply   = apply′

    ; isApplicative = record
        { app-ident        = app-ident′
        ; app-composition  = app-composition′
        ; app-homomorphism = λ x f → refl
        ; app-interchange  = app-interchange′

        ; app-fmap-unit    = app-fmap-unit′
        }
    }
  where
    apply′ : ∀ {E A B} → Either E (A → B) → Either E A → Either E B
    apply′ (Left e) _          = Left e
    apply′ _ (Left e)          = Left e
    apply′ (Right f) (Right x) = Right (f x)

    app-ident′ : ∀ {E A} (x : Either E A) → apply′ (Right id) x ≡ x
    app-ident′ (Left _)  = refl
    app-ident′ (Right _) = refl

    app-composition′
      : ∀ {E X Y Z} (u : Either E (Y → Z)) (v : Either E (X → Y)) (w : Either E X)
      → apply′ (apply′ (apply′ (Right (λ f g x → f (g x))) u) v) w
          ≡ apply′ u (apply′ v w)
    app-composition′ (Left _) _ _                  = refl
    app-composition′ (Right _) (Left _) _          = refl
    app-composition′ (Right _) (Right _) (Left _)  = refl
    app-composition′ (Right _) (Right _) (Right _) = refl

    app-interchange′ : ∀ {E X Y} (u : Either E (X → Y)) (y : X) →
                   apply′ u (Right y) ≡ apply′ (Right (λ f → f y)) u
    app-interchange′ (Left _) _  = refl
    app-interchange′ (Right _) _ = refl

    app-fmap-unit′ : ∀ {E X Y : Set} (f : X → Y) (x : Either E X)
                   → apply′ (Right f) x ≡ fmap f x
    app-fmap-unit′ _ (Left _)  = refl
    app-fmap-unit′ _ (Right _) = refl

EitherM : ∀ {E : Set} → Monad (Either E)
EitherM = record
    { base-functor = EitherF
    ; applicative  = EitherA

    ; join = join′

    ; isMonad = record
        { monad-law-1 = monad-law-1′
        ; monad-law-2 = monad-law-2′
        ; monad-law-3 = monad-law-3′
        ; monad-law-4 = λ f x → refl
        ; monad-law-5 = monad-law-5′
        }
    }
  where
    join′ : ∀ {E A} → Either E (Either E A) → Either E A
    join′ (Left e)         = Left e
    join′ (Right (Left e)) = Left e
    join′ (Right a)        = a

    monad-law-1′ : ∀ {E X} (x : Either E (Either E (Either E X))) →
               join′ (fmap {{EitherF}} join′ x) ≡ join′ (join′ x)
    monad-law-1′ (Left _) = refl
    monad-law-1′ (Right (Left _)) = refl
    monad-law-1′ (Right (Right (Left _))) = refl
    monad-law-1′ (Right (Right (Right _))) = refl

    monad-law-2′ : ∀ {E X} (x : Either E (Either E X)) →
               join′ (fmap {{EitherF}} Right x) ≡ x
    monad-law-2′ (Left _) = refl
    monad-law-2′ (Right (Left _)) = refl
    monad-law-2′ (Right (Right _)) = refl

    monad-law-3′ : ∀ {E X} (x : Either E X) → join′ (Right x) ≡ x
    monad-law-3′ (Left _) = refl
    monad-law-3′ (Right _) = refl

    monad-law-5′ : ∀ {E X Y} (f : X → Y) (x : Either E (Either E X)) →
               join′ (fmap {{EitherF}} (fmap {{EitherF}} f) x) ≡ fmap f (join′ x)
    monad-law-5′ f (Left _) = refl
    monad-law-5′ f (Right (Left _)) = refl
    monad-law-5′ f (Right (Right _)) = refl

data EitherT (E : Set) (M : Set → Set) (A : Set) : Set where
    mkEitherT : ∀ (m : M (Either E A)) → EitherT E M A

runEitherT : ∀ {E A B : Set} {M : Set → Set} → EitherT E M A → M (Either E A)
runEitherT (mkEitherT m) = m

EitherTF : ∀ {E : Set} {M : Set → Set} {{m-dict : Monad M}}
         → Functor (EitherT E M)
EitherTF {E} {M} {{m-dict}} = record
    { fmap = fmapM′

    ; isFunctor = record
        { fun-ident   = {!!} -- fun-ident′
        ; fun-compose = fun-compose′
        }
    }
  where
    fmapM′ : ∀ {X Y : Set} → (X → Y) → EitherT E M X → EitherT E M Y
    fmapM′ f (mkEitherT x) =
        mkEitherT (fmap {{base}} (fmap {{EitherF}} f) x)
      where
        base = Monad.base-functor m-dict

    fun-ident′ : ∀ {A} → (f : ∀ {B} → B → B) → (x : EitherT E M A) →
                   (∀ {B} {y : B} → f y ≡ y) → fmapM′ f x ≡ x
    fun-ident′ f (mkEitherT m) h =
        cong mkEitherT (IsFunctor.fun-ident {!!} f m h)
      where
        base     = Monad.base-functor m-dict
        fun-laws = Functor.isFunctor base

    fun-compose′ : ∀ {A B C : Set} (f : A → B) (g : B → C) (x : EitherT E M A)
               → fmapM′ (g ∘ f) x ≡ fmapM′ g (fmapM′ f x)
    fun-compose′ f g (mkEitherT x) =
        begin
            fmapM′ (g ∘ f) (mkEitherT x)
        ≡⟨ refl ⟩
            mkEitherT (fmap (fmap {{EitherF}} (g ∘ f)) x)
        ≡⟨ refl ⟩
            mkEitherT (fmap (λ y → fmap {{EitherF}} g (fmap {{EitherF}} f y)) x)
        ≡⟨ refl ⟩
            mkEitherT (fmap (λ y → fmap {{EitherF}} g (fmap {{EitherF}} f y)) x)
        ≡⟨ refl ⟩
            mkEitherT (fmap {{base}} (fmap {{EitherF}} g ∘ fmap {{EitherF}} f) x)
        ≡⟨ refl ⟩
            mkEitherT (fmap {{base}} (fmap {{EitherF}} g) (fmap {{base}} (fmap {{EitherF}} f) x))
        ≡⟨ refl ⟩
            fmapM′ g (fmapM′ f (mkEitherT x))
        ∎
      where
        base = Monad.base-functor m-dict

EitherTA : ∀ {E : Set} {M : Set → Set} {Monad M} → Applicative (EitherT E M)
EitherTA = record
    { functor = EitherTF

    ; pure    = pure ∘ Right
    ; apply   = apply′

    ; isApplicative = record
        { app-ident        = app-ident′
        ; app-composition  = app-composition′
        ; app-homomorphism = {!!}
        ; app-interchange  = app-interchange′

        ; app-fmap-unit    = app-fmap-unit′
        }
    }
  where
    apply′ : ∀ {E A B} {M : Set → Set} {Monad M}
           → EitherT E M (A → B) → EitherT E M A → EitherT E M B
    apply′ f x = {!!}

    app-ident′ : ∀ {E A} {M : Set → Set} {Monad M}
                   (x : EitherT E M A) → apply′ (pure (pure id)) x ≡ x
    app-ident′ x = {!!}

    app-composition′
      : ∀ {E X Y Z} {M : Set → Set} {Monad M}
          (u : EitherT E M (Y → Z)) (v : EitherT E M (X → Y)) (w : EitherT E M X)
      → apply′ (apply′ (apply′ (pure _$_) u) v) w
          ≡ apply′ u (apply′ v w)
    app-composition′ u v w = {!!}

    app-interchange′ : ∀ {E X Y} {M : Set → Set} {Monad M}
                         (u : EitherT E M (X → Y)) (y : X)
                     → apply′ u (pure y) ≡ apply′ (pure (λ f → f y)) u
    app-interchange′ u y = {!!}

    app-fmap-unit′ : ∀ {E X Y : Set} {M : Set → Set} {Monad M}
                       (f : X → Y) (x : EitherT E M X)
                   → apply′ (pure f) x ≡ fmap f x
    app-fmap-unit′ f x = {!!}

EitherTM : ∀ {E : Set} {M : Set → Set} {Monad M} → Monad (EitherT E M)
EitherTM = record
    { base-functor = EitherTF
    ; applicative  = EitherTA

    ; join = join′

    ; isMonad = record
        { monad-law-1 = monad-law-1′
        ; monad-law-2 = monad-law-2′
        ; monad-law-3 = monad-law-3′
        ; monad-law-4 = {!!}
        ; monad-law-5 = monad-law-5′
        }
    }
  where
    join′ : ∀ {E A} {M : Set → Set} {Monad M}
          → EitherT E M (EitherT E M A) → EitherT E M A
    join′ x = {!!}

    monad-law-1′ : ∀ {E X} {M : Set → Set} {Monad M}
                     (x : EitherT E M (EitherT E M (EitherT E M X)))
                 → join′ (fmap {{EitherTF}} join′ x) ≡ join′ (join′ x)
    monad-law-1′ x = {!!}

    monad-law-2′ : ∀ {E X} {M : Set → Set} {Monad M}
                     (x : EitherT E M (EitherT E M X))
                 → join′ (fmap {{EitherTF}} pure x) ≡ x
    monad-law-2′ x = {!!}

    monad-law-3′ : ∀ {E X} {M : Set → Set} {Monad M}
                     (x : EitherT E M X)
                 → join′ (pure x) ≡ x
    monad-law-3′ x = {!!}

    monad-law-5′ : ∀ {E X Y} {M : Set → Set} {Monad M}
                     (f : X → Y) (x : EitherT E M (EitherT E M X))
                 → join′ (fmap {{EitherTF}} (fmap {{EitherTF}} f) x)
                     ≡ fmap f (join′ x)
    monad-law-5′ f x = {!!}
