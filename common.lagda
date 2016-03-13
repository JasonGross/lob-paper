\section{Standard Data-Type Declarations} \label{sec:common}
 \AgdaHide{
  \begin{code}
module common where
  \end{code}
}
\begin{code}
open import Agda.Primitive public
  using    (Level; _⊔_; lzero; lsuc)

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
