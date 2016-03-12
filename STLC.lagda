Some preliminary definitions

\begin{code}
open import Function
data ⊥ : Set where
record ⊤ : Set where constructor <>

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field π₁ : A
        π₂ : B π₁

open Σ

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

if+ : ∀{A B C : Set} → (A → C) → (B → C) → (A + B → C)
if+ l r (inl x) = l x
if+ l r (inr x) = r x

data List (A : Set) : Set where
  ε : List A
  _::_ : A → List A → List A

_++_ : ∀{A} → List A → List A → List A
ε ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)
\end{code}

Next we will define the types in our simple system.
These will be the standard type formers of the simply typed lambda calculus,
with one key extension. We add a type former _‘⊢’_ which is meant to reflect the type of terms.

\begin{code}
infixr 5 _⊢_ _‘⊢’_
infixr 10 _‘→’_ _‘+’_ _‘×’_

data ⋆ : Set where
  _‘⊢’_ : List ⋆ → ⋆ → ⋆
  _‘→’_ _‘×’_ _‘+’_ : ⋆ → ⋆ → ⋆
  ‘0’ ‘1’ : ⋆

Con = List ⋆
\end{code}

We will then need some way to handle binding.
For reasons of simplicity, we'll make use of a dependent form of DeBrujin variables.

\begin{code}
data _∈_ (T : ⋆) : Con → Set where
\end{code}

First we want our "variable zero", which lets us pick off the ``top'' element of the context.

\begin{code}
  top : ∀{Γ} → T ∈ (T :: Γ)
\end{code}

Then we want a way to extend variables to work in larger contexts.

\begin{code}
  pop : ∀{Γ S} → T ∈ Γ → T ∈ (S :: Γ)
\end{code}

And, finally, we are ready to define the term language for our extended STLC.

\begin{code}
data _⊢_ (Γ : Con) : ⋆ → Set where
\end{code}

The next few constructors are fairly standard.
Before anything else, we want to be able to lift bindings into terms.

\begin{code}
  var : ∀{T} → T ∈ Γ → Γ ⊢ T
\end{code}

Then the intro rules for all of our easier datatypes.
0 has no constructors, 1 has one.
The product requires both its inputs, and the coproduct takes one.

\begin{code}
  tt : Γ ⊢ ‘1’
  _,_ : ∀{A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ‘×’ B
  inl : ∀{A B} → Γ ⊢ A → Γ ⊢ A ‘+’ B
  inr : ∀{A B} → Γ ⊢ B → Γ ⊢ A ‘+’ B
\end{code}

The elimination rules have a nice symmetry.
Where 1 only has an introduction rule, 0 only has an elimination rule.
The intro/elim rule counts of the product and coproduct have been similarly swapped.

\begin{code}
  frec : ∀{A} → Γ ⊢ ‘0’ → Γ ⊢ A
  sump : ∀{A B C} → Γ ⊢ (A ‘→’ C) → Γ ⊢ (B ‘→’ C) → Γ ⊢ A ‘+’ B → Γ ⊢ C
  fst : ∀{A B} → Γ ⊢ A ‘×’ B → Γ ⊢ A
  snd : ∀{A B} → Γ ⊢ A ‘×’ B → Γ ⊢ B
\end{code}

Then, of course, we need to handle function types.
Lambdas are handled in essentially the same way as in the dependent formalism, but with simple codomains rather than dependent ones.
Similarly, application can avoid the complications of dependent substitution, and just return the concrete codomain type.

\begin{code}
  lam : ∀{A B} → (A :: Γ) ⊢ B → Γ ⊢ (A ‘→’ B)
  _#_ : ∀{A B} → Γ ⊢ (A ‘→’ B) → Γ ⊢ A → Γ ⊢ B
\end{code}

At this point things become more delicate.
To properly capture GL, we want our theory to validate the rules

\begin{enumerate}
\item ⊢ A → ⊢ □ A
\item ⊢ □ A ‘→’ □ □ A
\end{enumerate}

But \emph{not} ⊢ A ‘→’ □ A.
If we only had the unary □ operator we would run into difficulty later.
Crucially, we couldn't add the rule (Γ ⊢ A → Γ ⊢ □ A), since this would let us prove A ‘→’ □ A.

But, luckily enough, we didn't restrict ourselves in this way.
Instead we took as primitive the more general notion of provability in a context, and this lets us give a proper account of □ without compromising on strength.

We will denote by Gödel quotes the constructor corresponding to rule 1.

\begin{code}
  ⌜_⌝ : ∀{Δ A} → Δ ⊢ A → Γ ⊢ (Δ ‘⊢’ A)
\end{code}

Similarly, we will write the rule validating ``□ A ‘→’ □ □ A'' as ``quot''.

\begin{code}
  quot : ∀{Δ A} → Γ ⊢ (Δ ‘⊢’ A) → Γ ⊢ (Δ ‘⊢’ (Δ ‘⊢’ A)) -- from □ A -> □ (□ A)
\end{code}

We would like to be able to apply functions under □, and for this we introduce the so-called ``distribution'' rule.
In GL it takes the form ``⊢ □ (A ‘→’ B) → ⊢ (□ A ‘→’ □ B)''.
For us it is not much more complicated.

\begin{code}
  dist : ∀{Δ A B} → Γ ⊢ (Δ ‘⊢’ (A ‘→’ B)) → Γ ⊢ (Δ ‘⊢’ A) → Γ ⊢ (Δ ‘⊢’ B)
\end{code}

And, finally, we include the Lobian axiom, translated to the new contextual provability type.

\begin{code}
  Lob : ∀{Δ A} → Γ ⊢ (Δ ‘⊢’ ((Δ ‘⊢’ A) ‘→’ A)) → Γ ⊢ (Δ ‘⊢’ A)
\end{code}

We also specify a fixity for function application.
\begin{code}
infixl 50 _#_
\end{code}

From these constructors we can prove the simpler form of the Lob rule.

\begin{code}
lob : ∀{Γ A} → Γ ⊢ ((Γ ‘⊢’ A) ‘→’ A) → Γ ⊢ A
lob t = t # Lob ⌜ t ⌝
\end{code}

Of course, because we are using DeBrujin indices, before we can do too much we'll need to give an account of lifting.
Thankfully, unlike when we were dealing with dependent type theory, we can define these computationally, and get for free all the congruences we had to add as axioms before.

Our definition of weakening is unremarkable, but we've included it below as a reference.
One surprising and nice aspect of these definitions is that they were fully automatic - each right hand side generated by Agsy without any hinting.

\begin{code}
lift-var : ∀{Γ A} T Δ → A ∈ (Δ ++ Γ) → A ∈ (Δ ++ (T :: Γ))
lift-var T ε v = pop v
lift-var T (A :: Δ) top = top
lift-var T (x :: Δ) (pop v) = pop (lift-var T Δ v)

lift : ∀{Γ A} T Δ → (Δ ++ Γ) ⊢ A → (Δ ++ (T :: Γ)) ⊢ A
lift T Δ (var x) = var (lift-var T Δ x)
lift T Δ tt = tt
lift T Δ (a , b) = lift T Δ a , lift T Δ b
lift T Δ (inl t) = inl (lift T Δ t)
lift T Δ (inr t) = inr (lift T Δ t)
lift T Δ (frec t) = frec (lift T Δ t)
lift T Δ (sump t t₁ t₂) = sump (lift T Δ t) (lift T Δ t₁) (lift T Δ t₂)
lift T Δ (fst t) = fst (lift T Δ t)
lift T Δ (snd t) = snd (lift T Δ t)
lift T Δ (lam t) = lam (lift T (_ :: Δ) t)
lift T Δ (t # t₁) = lift T Δ t # lift T Δ t₁
lift T Δ ⌜ t ⌝ = ⌜ t ⌝
lift T Δ (quot t) = quot (lift T Δ t)
lift T Δ (dist t t₁) = dist (lift T Δ t) (lift T Δ t₁)
lift T Δ (Lob t) = Lob (lift T Δ t)
\end{code}

Having defined lifting at all levels, we can give weakening as a special case.

\begin{code}
wk : ∀{Γ A B} → Γ ⊢ A → (B :: Γ) ⊢ A
wk = lift _ ε
\end{code}

Finally, we define function composition for our internal language.

\begin{code}
infixl 10 _∘'_
_∘'_ : ∀{Γ A B C} → Γ ⊢ (B ‘→’ C) → Γ ⊢ (A ‘→’ B) → Γ ⊢ (A ‘→’ C)
f ∘' g = lam (wk f # (wk g # var top))
\end{code}

Now we are ready to prove that FairBot cooperates with itself.
Sadly, our type system isn't expressive enough to give a general type of bots, but we can still prove things about the interactions of particular bots if we substitute their types by hand.
For example, we can state the desired theorem (that FairBot cooperates with itself) as:

\begin{code}
distf : ∀{Γ Δ A B} → Γ ⊢ (Δ ‘⊢’ A ‘→’ B) → Γ ⊢ (Δ ‘⊢’ A) ‘→’ (Δ ‘⊢’ B)
distf bf = lam (dist (wk bf) (var top))

evf : ∀{Γ Δ A} → Γ ⊢ (Δ ‘⊢’ A) ‘→’ (Δ ‘⊢’ (Δ ‘⊢’ A))
evf = lam (quot (var top))

fb-fb-cooperate : ∀{Γ A B} → Γ ⊢ (Γ ‘⊢’ A) ‘→’ B → Γ ⊢(Γ ‘⊢’ B) ‘→’ A → Γ ⊢ (A ‘×’ B)
fb-fb-cooperate a b = lob (b ∘' distf ⌜ a ⌝ ∘' evf) , lob (a ∘' distf ⌜ b ⌝ ∘' evf)
\end{code}

We can also state the theorem in a more familiar form with a couple abbreviations
\begin{code}
‘□’ = _‘⊢’_ ε
□ = _⊢_ ε

fb-fb-cooperate' : ∀{A B} → □ (‘□’ A ‘→’ B) → □ (‘□’ B ‘→’ A) → □ (A ‘×’ B)
fb-fb-cooperate' = fb-fb-cooperate
\end{code}

We'd also like to show all the metatheoretic properites we had before: soundness, inhabitedness, and incompleteness.
We can show inhabitedness immediately in several different ways. We'll take the easiest one.

\begin{code}
inhabited : Σ ⋆ λ T → ε ⊢ T
inhabited = ‘1’ , tt
\end{code}

To prove soundness and incompleteness we'll first need to give the standard interpretation.
Again, the simplicity of our system makes our lives easier.
We define the interpreter for types as follows:

\begin{code}
⟦_⟧⋆ : ⋆ → Set
⟦ Δ ‘⊢’ T ⟧⋆ = Δ ⊢ T
⟦ A ‘→’ B ⟧⋆ = ⟦ A ⟧⋆ → ⟦ B ⟧⋆
⟦ A ‘×’ B ⟧⋆ = ⟦ A ⟧⋆ × ⟦ B ⟧⋆
⟦ A ‘+’ B ⟧⋆ = ⟦ A ⟧⋆ + ⟦ B ⟧⋆
⟦ ‘0’ ⟧⋆ = ⊥
⟦ ‘1’ ⟧⋆ = ⊤
\end{code}

The interpreter for contexts is simplified - we only need simple products to interpret simple contexts.
\begin{code}
⟦_⟧c : Con → Set
⟦ ε ⟧c = ⊤
⟦ x :: Γ ⟧c = ⟦ Γ ⟧c × ⟦ x ⟧⋆
\end{code}

\begin{code}
ᵏ : {A B : Set} → A → B → A
ᵏ a b = a

ᵛ : ∀ {S T}{P : Σ S T → Set}
    → ((s : S) (t : T s) → P (s , t))
    → (σ : Σ S T) → P σ
ᵛ f (s , t) = f s t

^ : ∀ {S T}{P : Σ S T → Set}
    → ((σ : Σ S T) → P σ)
    → (s : S) (t : T s) → P (s , t)
^ f s t = f (s , t)
\end{code}

We can then interpret variables in any interpretable context.

\begin{code}
⟦_⟧v : ∀{Γ A} → A ∈ Γ → ⟦ Γ ⟧c → ⟦ A ⟧⋆
⟦ top ⟧v = π₂
⟦ pop v ⟧v = ⟦ v ⟧v ∘ π₁
\end{code}

And now we can interpret terms.

\begin{code}
⟦_⟧t : ∀{Γ A} → Γ ⊢ A → ⟦ Γ ⟧c → ⟦ A ⟧⋆
⟦ var v ⟧t = ⟦ v ⟧v
⟦ tt ⟧t = ᵏ <>
⟦ a , b ⟧t = ᵏ _,_ ˢ ⟦ a ⟧t ˢ ⟦ b ⟧t
⟦ inl a ⟧t = ᵏ inl ˢ ⟦ a ⟧t
⟦ inr b ⟧t = ᵏ inr ˢ ⟦ b ⟧t
⟦ frec t ⟧t = ᵏ (λ ()) ˢ ⟦ t ⟧t
⟦ sump l r s ⟧t = ᵏ if+ ˢ ⟦ l ⟧t ˢ ⟦ r ⟧t ˢ ⟦ s ⟧t
⟦ fst t ⟧t = ᵏ π₁ ˢ ⟦ t ⟧t
⟦ snd t ⟧t = ᵏ π₂ ˢ ⟦ t ⟧t
⟦ lam b ⟧t = ^ ⟦ b ⟧t
⟦ f # x ⟧t = ⟦ f ⟧t ˢ ⟦ x ⟧t
⟦ ⌜ t ⌝ ⟧t = ᵏ t
⟦ quot t ⟧t = ᵏ ⌜_⌝ ˢ ⟦ t ⟧t
⟦ dist f x ⟧t = ᵏ _#_ ˢ ⟦ f ⟧t ˢ ⟦ x ⟧t
⟦ Lob l ⟧t = ᵏ lob ˢ ⟦ l ⟧t
\end{code}

Now we can prove all the things we wanted.

\begin{code}
¬ : Set → Set
¬ T = T → ⊥
‘¬’_ : ⋆ → ⋆
‘¬’ T = T ‘→’ ‘0’

consistency : ¬ (□ ‘0’)
consistency f = ⟦ f ⟧t <>

incompleteness : ¬ (□ (‘¬’ ‘□’ ‘0’))
incompleteness t = ⟦ lob t ⟧t <>

soundness : ∀{A} → □ A → ⟦ A ⟧⋆
soundness a = ⟦ a ⟧t <>
\end{code}
