\section{Standard Data-Type Declarations} \label{sec:common}
 \AgdaHide{
  \begin{code}
module common where
  \end{code}
}
\begin{code}
open import Agda.Primitive public
  using    (Level; _⊔_; lzero; lsuc)

_∘_ : ∀ {i j k}{A : Set i}{B : A → Set j}{C : {x : A} → B x → Set k}
      → ({x : A} (y : B x) → C y) → (g : (x : A) → B x) (x : A) → C (g x)
f ∘ g = λ x → f (g x)

infixl 8 _ˢ_

_ˢ_ : ∀ {i j k}{A : Set i}{B : A → Set j}{C : (x : A) → B x → Set k}
      → ((x : A) (y : B x) → C x y)
      → (g : (x : A) → B x) (x : A) → C x (g x)
f ˢ g = λ x → f x (g x)

ᵏ : {A B : Set} → A → B → A
ᵏ a b = a

infixl 1 _,_
infixr 2 _×_
infixl 1 _≡_

record ⊤ {ℓ} : Set ℓ where
  constructor tt

data ⊥ {ℓ} : Set ℓ where

¬_ : ∀ {ℓ ℓ′} → Set ℓ → Set (ℓ ⊔ ℓ′)
¬_ {ℓ} {ℓ′} T = T → ⊥ {ℓ′}

record Σ {a p} (A : Set a) (P : A → Set p)
         : Set (a ⊔ p)
       where
  constructor _,_
  field
    fst : A
    snd : P fst

open Σ public

ᵛ : ∀ {i j k}{S : Set i}{T : S → Set j}{P : Σ S T → Set k}
    → ((s : S) (t : T s) → P (s , t))
    → (σ : Σ S T) → P σ
ᵛ f (s , t) = f s t

^ : ∀ {i j k}{S : Set i}{T : S → Set j}{P : Σ S T → Set k}
    → ((σ : Σ S T) → P σ)
    → (s : S) (t : T s) → P (s , t)
^ f s t = f (s , t)

data _+_ {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  inl : A → A + B
  inr : B → A + B

if+ : ∀{A B C : Set} → (A → C) → (B → C) → (A + B → C)
if+ l r (inl x) = l x
if+ l r (inr x) = r x

data Lifted {a b} (A : Set a) : Set (b ⊔ a) where
  lift : A → Lifted A

lower : ∀ {a b A} → Lifted {a} {b} A → A
lower (lift x) = x

_×_ : ∀ {ℓ ℓ′} (A : Set ℓ) (B : Set ℓ′) → Set (ℓ ⊔ ℓ′)
A × B = Σ A (λ _ → B)

data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

sym : {A : Set} → {x : A} → {y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

transport : ∀ {A : Set} {x : A} {y : A} → (P : A → Set)
  → x ≡ y → P x → P y
transport P refl v = v

data List (A : Set) : Set where
  ε : List A
  _::_ : A → List A → List A

_++_ : ∀{A} → List A → List A → List A
ε ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

\end{code}
