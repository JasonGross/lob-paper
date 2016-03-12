\section{Self cooperation in STLC} \label{sec:STLC}

\AgdaHide{
  \begin{code}
module STLC where
open import common
  \end{code}
}

We'll make use of a few particularly useful dependent combinators throughout this section - they're defined below.
\begin{code}
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

^ : ∀ {i j k}{S : Set i}{T : S → Set j}{P : Σ S T → Set k}
    → ((σ : Σ S T) → P σ)
    → (s : S) (t : T s) → P (s , t)
^ f s t = f (s , t)
\end{code}

It turns out that we can define all the things we need to prove self-cooperation of FairBot in a variant of the simply typed lambda calculus.
In order to do this, however, we have to define \mintinline{Agda}|□| somewhat differently.
Particularly, we abandon the notion of a unary \mintinline{Agda}|□| and instead base our theory on a binary operator denoting provability in a context.

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

\begin{code}
  <> : Γ ⊢ ‘1’
  _,_ : ∀{A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ‘×’ B
  inl : ∀{A B} → Γ ⊢ A → Γ ⊢ A ‘+’ B
  inr : ∀{A B} → Γ ⊢ B → Γ ⊢ A ‘+’ B
  ‘0’-elim : ∀{A} → Γ ⊢ ‘0’ → Γ ⊢ A
  ‘+’-elim : ∀{A B C} → Γ ⊢ (A ‘→’ C) → Γ ⊢ (B ‘→’ C) → Γ ⊢ A ‘+’ B → Γ ⊢ C
  π₁ : ∀{A B} → Γ ⊢ A ‘×’ B → Γ ⊢ A
  π₂ : ∀{A B} → Γ ⊢ A ‘×’ B → Γ ⊢ B
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
\item \mintinline{Agda}|⊢ A → ⊢ □ A|
\item \mintinline{Agda}|⊢ □ A ‘→’ □ □ A|
\end{enumerate}

But \emph{not} \mintinline{Agda}|⊢ A ‘→’ □ A|.
If we only had the unary \mintinline{Agda}|□| operator we would run into difficulty later.
Crucially, we couldn't add the rule \mintinline{Agda}|Γ ⊢ A → Γ ⊢ □ A|, since this would let us prove \mintinline{Agda}|A ‘→’ □ A|.

But, luckily enough, we didn't restrict ourselves in this way.
Instead we took as primitive the more general notion of provability in a context, and this lets us give a proper account of \mintinline{Agda}|□| without compromising on strength.

We will denote by Gödel quotes the constructor corresponding to rule 1.

\begin{code}
  ⌜_⌝ : ∀{Δ A} → Δ ⊢ A → Γ ⊢ (Δ ‘⊢’ A)
\end{code}

Similarly, we will write the rule validating \mintinline{Agda}|□ A ‘→’ □ □ A| as \mintinline{Agda}|quot|.

\begin{code}
  quot : ∀{Δ A} → Γ ⊢ (Δ ‘⊢’ A) → Γ ⊢ (Δ ‘⊢’ (Δ ‘⊢’ A)) -- from □ A -> □ (□ A)
\end{code}

We would like to be able to apply functions under \mintinline{Agda}|□|, and for this we introduce the so-called ``distribution'' rule.
In GL it takes the form \mintinline{Agda}|⊢ □ (A ‘→’ B) → ⊢ (□ A ‘→’ □ B)|.
For us it is not much more complicated.

\begin{code}
  dist : ∀{Δ A B} → Γ ⊢ (Δ ‘⊢’ (A ‘→’ B)) → Γ ⊢ (Δ ‘⊢’ A) → Γ ⊢ (Δ ‘⊢’ B)
\end{code}

And, finally, we include the Löbian axiom, translated to the new contextual provability type.

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

lift-tm : ∀{Γ A} T Δ → (Δ ++ Γ) ⊢ A → (Δ ++ (T :: Γ)) ⊢ A
lift-tm T Δ (var x) = var (lift-var T Δ x)
lift-tm T Δ <> = <>
lift-tm T Δ (a , b) = lift-tm T Δ a , lift-tm T Δ b
lift-tm T Δ (inl t) = inl (lift-tm T Δ t)
lift-tm T Δ (inr t) = inr (lift-tm T Δ t)
lift-tm T Δ (‘0’-elim t) = ‘0’-elim (lift-tm T Δ t)
lift-tm T Δ (‘+’-elim t t₁ t₂) = ‘+’-elim (lift-tm T Δ t) (lift-tm T Δ t₁) (lift-tm T Δ t₂)
lift-tm T Δ (π₁ t) = π₁ (lift-tm T Δ t)
lift-tm T Δ (π₂ t) = π₂ (lift-tm T Δ t)
lift-tm T Δ (lam t) = lam (lift-tm T (_ :: Δ) t)
lift-tm T Δ (t # t₁) = lift-tm T Δ t # lift-tm T Δ t₁
lift-tm T Δ ⌜ t ⌝ = ⌜ t ⌝
lift-tm T Δ (quot t) = quot (lift-tm T Δ t)
lift-tm T Δ (dist t t₁) = dist (lift-tm T Δ t) (lift-tm T Δ t₁)
lift-tm T Δ (Lob t) = Lob (lift-tm T Δ t)
\end{code}

Having defined lift-tming at all levels, we can give weakening as a special case.

\begin{code}
wk : ∀{Γ A B} → Γ ⊢ A → (B :: Γ) ⊢ A
wk = lift-tm _ ε
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
inhabited = ‘1’ , <>
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

We can then interpret variables in any interpretable context.

\begin{code}
⟦_⟧v : ∀{Γ A} → A ∈ Γ → ⟦ Γ ⟧c → ⟦ A ⟧⋆
⟦ top ⟧v = snd
⟦ pop v ⟧v = ⟦ v ⟧v ∘ fst
\end{code}

And now we can interpret terms.

\begin{code}
⟦_⟧t : ∀{Γ A} → Γ ⊢ A → ⟦ Γ ⟧c → ⟦ A ⟧⋆
⟦ var v ⟧t = ⟦ v ⟧v
⟦ <> ⟧t = ᵏ _
⟦ a , b ⟧t = ᵏ _,_ ˢ ⟦ a ⟧t ˢ ⟦ b ⟧t
⟦ inl a ⟧t = ᵏ inl ˢ ⟦ a ⟧t
⟦ inr b ⟧t = ᵏ inr ˢ ⟦ b ⟧t
⟦ ‘0’-elim t ⟧t = ᵏ (λ ()) ˢ ⟦ t ⟧t
⟦ ‘+’-elim l r s ⟧t = ᵏ if+ ˢ ⟦ l ⟧t ˢ ⟦ r ⟧t ˢ ⟦ s ⟧t
⟦ π₁ t ⟧t = ᵏ fst ˢ ⟦ t ⟧t
⟦ π₂ t ⟧t = ᵏ snd ˢ ⟦ t ⟧t
⟦ lam b ⟧t = ^ ⟦ b ⟧t
⟦ f # x ⟧t = ⟦ f ⟧t ˢ ⟦ x ⟧t
⟦ ⌜ t ⌝ ⟧t = ᵏ t
⟦ quot t ⟧t = ᵏ ⌜_⌝ ˢ ⟦ t ⟧t
⟦ dist f x ⟧t = ᵏ _#_ ˢ ⟦ f ⟧t ˢ ⟦ x ⟧t
⟦ Lob l ⟧t = ᵏ lob ˢ ⟦ l ⟧t
\end{code}

Which lets us prove all our sanity checks.

\begin{code}
‘¬’_ : ⋆ → ⋆
‘¬’ T = T ‘→’ ‘0’

consistency : ¬ (□ ‘0’)
consistency f = ⟦ f ⟧t tt

incompleteness : ¬ (□ (‘¬’ ‘□’ ‘0’))
incompleteness t = ⟦ lob t ⟧t tt

soundness : ∀{A} → □ A → ⟦ A ⟧⋆
soundness a = ⟦ a ⟧t tt
\end{code}
