
module Grep where

open import Prelude
open import Data.Traversable using (mapM)
open import Text.Printf
open import Lists

lines′ : List Char → List String
lines′ [] = []
lines′ ('\r' ∷ '\n' ∷ s) = "" ∷ lines′ s
lines′ ('\n' ∷ s)        = "" ∷ lines′ s
lines′ (c ∷ s)           = cons c (lines′ s)
  where
    cons : Char → List String → List String
    cons c (s ∷ ss) = (packString [ c ] & s) ∷ ss
    cons c [] = packString [ c ] ∷ []

lines : String → List String
lines = lines′ ∘ unpackString

words′ : List Char → List String
words′ [] = []
words′ (' ' ∷ s) = "" ∷ words′ s
words′ (c ∷ s)   = cons c (words′ s)
  where
    cons : Char → List String → List String
    cons c (s ∷ ss) = (packString [ c ] & s) ∷ ss
    cons c [] = packString [ c ] ∷ []

words : String → List String
words = words′ ∘ unpackString

-- Bonus exercise: Line numbers
--   Compute and print line numbers (represented by _∈_ or Any)
--   Might be useful to implement a variant of filterMaybe:
--     filterMaybeIx : {A : Set} {P : A → Set} → (∀ x → Maybe (P x)) →
--                     (xs : List A) → List (Σ A (λ x → x ∈ xs × P x))

private
  suc′ : ∀ {A} {P : A → Set} {x : A} {xs : List A} →
         Σ A (λ x₁ → Σ (Any (_≡_ x₁) xs) (λ _ → P x₁)) →
         Σ A (λ x₁ → Σ (Any (_≡_ x₁) (x ∷ xs)) (λ _ → P x₁))
  suc′ (x , p , y) = x , suc p , y

Result : ∀ A xs (P : A → Set) → Set
Result A xs P = Σ A (λ x → x ∈ xs × P x)

filterMaybeIx : {A : Set} {P : A → Set}
              → (∀ x → Maybe (P x)) → (xs : List A)
              → List (Result A xs P)
filterMaybeIx p [] = []
filterMaybeIx p (x ∷ xs) with (p x)
filterMaybeIx p (x ∷ xs) | nothing = rest
  where rest = suc′ <$> filterMaybeIx p xs
filterMaybeIx p (x ∷ xs) | just x₁ = (x , zero refl , x₁) ∷ rest
  where rest = suc′ <$> filterMaybeIx p xs

-- Bonus exercise: More interesting matching
--   data Inside {A : Set} (xs ys : List A) : Set where
--     inside : ∀ pre suf → ys ≡ pre ++ xs ++ suf → Inside xs ys
--   Match word s = Inside (unpackString word) (unpackString s)

FoundWord : ∀ word → ((s : String) → Set)
FoundWord word = λ s → word ∈ words s

FoundLine : ∀ (word : String) → ((s : String) → Set)
FoundLine word = λ s → word ≡ s

match : ∀ word s → Maybe (FoundWord word s)
match word s = find word (words s)

matchWholeLine : ∀ word s → Maybe (FoundLine word s)
matchWholeLine word s with (word == s)
matchWholeLine word s | yes x = just x
matchWholeLine word s | no x = nothing

Result′ : ∀ word xs → Set
Result′ word xs =
  Result String xs (λ s → Either (FoundWord word s) (FoundLine word s))

grep : ∀ word s → List (Result′ word (lines s))
grep word s = filterMaybeIx go (lines s)
  where
    go : ∀ s → Maybe (Either (FoundWord word s) (FoundLine word s))
    go s = maybe (right <$> matchWholeLine word s) (just ∘ left) (match word s)

printLine : ∀ {xs} word → Result′ word xs → IO Unit
printLine word (s , p , m) = putStrLn $ printf "%d: %s" (count p) s
  where
    count : ∀ {A : Set} {x : A} {xs : List A} → x ∈ xs → Nat
    count (zero p₁) = 1
    count (suc xs₁) = 1 + count xs₁

main : IO Unit
main =
  getArgs >>= λ args →
  case args of
  λ { (word ∷ file ∷ []) →
      readFile file >>= λ s →
      unit <$ mapM (printLine word) (grep word s)
    ; _ →
      getProgName >>= λ prog →
      putStrLn ("USAGE: " & prog & " WORD FILE")
    }
