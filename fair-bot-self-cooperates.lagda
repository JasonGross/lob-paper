\section{Proving that FairBot Cooperates with Itself} \label{sec:fair-bot-self-cooperates}

\AgdaHide{
  \begin{code}
module fair-bot-self-cooperates where
open import common
  \end{code}
}

We begin with the definitions of a few particularly useful dependent
combinators:

\begin{code}
_∘_ : ∀ {A : Set}
  {B : A → Set}
  {C : {x : A} → B x → Set}
  → ({x : A} (y : B x) → C y)
  → (g : (x : A) → B x) (x : A)
  → C (g x)
f ∘ g = λ x → f (g x)

infixl 8 _ˢ_

_ˢ_ : ∀ {A : Set}
  {B : A → Set}
  {C : (x : A) → B x → Set}
  → ((x : A) (y : B x) → C x y)
  → (g : (x : A) → B x) (x : A)
  → C x (g x)
f ˢ g = λ x → f x (g x)

ᵏ : {A B : Set} → A → B → A
ᵏ a b = a

^ : ∀ {S : Set} {T : S → Set} {P : Σ S T → Set}
    → ((σ : Σ S T) → P σ)
    → (s : S) (t : T s) → P (s , t)
^ f s t = f (s , t)
\end{code}

It turns out that we can define all the things we need for proving
self-cooperation of FairBot in a variant of the simply typed lambda
calculus (STLC).  In order to do this, we do not index types over
contexts.  Rather than using \mintinline{Agda}|Term {Γ} T|, we will
denote the type of terms in context \mintinline{Agda}|Γ| of type
\mintinline{Agda}|T| as \mintinline{Agda}|Γ ⊢ T|, the standard
notation for ``provability''.  Since our types are no longer indexed
over contexts, we can represent a context as a list of types.

\begin{code}
infixr 5 _⊢_ _‘⊢’_
infixr 10 _‘→’_ _‘×’_

data Type : Set where
  _‘⊢’_ : List Type → Type → Type
  _‘→’_ _‘×’_ : Type → Type → Type
  ‘⊥’ ‘⊤’ : Type

Context = List Type
\end{code}

We will then need some way to handle binding.
For simplicity, we'll make use of a dependent form of DeBrujin variables.

\begin{code}
data _∈_ (T : Type) : Context → Set where
\end{code}

First we want our ``variable zero'', which lets us pick off the ``top'' element of the context.

\begin{code}
  top : ∀ {Γ} → T ∈ (T :: Γ)
\end{code}

Then we want a way to extend variables to work in larger contexts.

\begin{code}
  pop : ∀ {Γ S} → T ∈ Γ → T ∈ (S :: Γ)
\end{code}

And, finally, we are ready to define the term language for our extended STLC.

\begin{code}
data _⊢_ (Γ : Context) : Type → Set where
\end{code}

The next few constructors are fairly standard.
Before anything else, we want to be able to lift bindings into terms.

\begin{code}
  var : ∀ {T} → T ∈ Γ → Γ ⊢ T
\end{code}

Then the intro rules for all of our easier datatypes.

\begin{code}
  <> : Γ ⊢ ‘⊤’
  _,_ : ∀ {A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ‘×’ B
  ‘⊥’-elim : ∀ {A} → Γ ⊢ ‘⊥’ → Γ ⊢ A
  π₁ : ∀ {A B} → Γ ⊢ A ‘×’ B → Γ ⊢ A
  π₂ : ∀ {A B} → Γ ⊢ A ‘×’ B → Γ ⊢ B
  ‘λ’ : ∀ {A B} → (A :: Γ) ⊢ B → Γ ⊢ (A ‘→’ B)
  _‘’ₐ_ : ∀ {A B} → Γ ⊢ (A ‘→’ B) → Γ ⊢ A → Γ ⊢ B
\end{code}

At this point things become more delicate.
To properly capture Gӧdel--Lӧb modal logic, abbreviated as GL, we want our theory to validate the rules

\begin{enumerate}
\item \mintinline{Agda}|⊢ A → ⊢ □ A|
\item \mintinline{Agda}|⊢ □ A ‘→’ □ □ A|
\end{enumerate}

However, it should \emph{not} validate \mintinline{Agda}|⊢ A ‘→’ □ A|.
If we only had the unary \mintinline{Agda}|□| operator we would run into difficulty later.
Crucially, we couldn't add the rule \mintinline{Agda}|Γ ⊢ A → Γ ⊢ □ A|, since this would let us prove \mintinline{Agda}|A ‘→’ □ A|.

We will use Gödel quotes to denote the constructor corresponding to rule 1:

\begin{code}
  ⌜_⌝ : ∀ {Δ A} → Δ ⊢ A → Γ ⊢ (Δ ‘⊢’ A)
\end{code}

Similarly, we will write the rule validating \mintinline{Agda}|□ A ‘→’ □ □ A| as \mintinline{Agda}|repr|.

\begin{code}
  repr : ∀ {Δ A} → Γ ⊢ (Δ ‘⊢’ A) → Γ ⊢ (Δ ‘⊢’ (Δ ‘⊢’ A))
\end{code}

We would like to be able to apply functions under \mintinline{Agda}|□|, and for this we introduce the so-called ``distribution'' rule.
In GL, it takes the form \mintinline{Agda}|⊢ □ (A ‘→’ B) → ⊢ (□ A ‘→’ □ B)|.
For us it is not much more complicated.

\begin{code}
  dist : ∀ {Δ A B}
    → Γ ⊢ (Δ ‘⊢’ (A ‘→’ B))
    → Γ ⊢ (Δ ‘⊢’ A)
    → Γ ⊢ (Δ ‘⊢’ B)
\end{code}

And, finally, we include the Löbian axiom.

\begin{code}
  Lӧb : ∀ {Δ A}
    → Γ ⊢ (Δ ‘⊢’ ((Δ ‘⊢’ A) ‘→’ A))
    → Γ ⊢ (Δ ‘⊢’ A)
\end{code}

\AgdaHide{
\begin{code}
infixl 50 _‘’ₐ_
\end{code}
}

From these constructors we can prove the simpler form of the Lӧb rule.

\begin{code}
lӧb : ∀ {Γ A} → Γ ⊢ ((Γ ‘⊢’ A) ‘→’ A) → Γ ⊢ A
lӧb t = t ‘’ₐ Lӧb ⌜ t ⌝
\end{code}

Of course, because we are using DeBrujin indices, before we can do too much we'll need to give an account of lifting.
Thankfully, unlike when we were dealing with dependent type theory, we can define these computationally, and get for free all the congruences we had to add as axioms before.

Our definition of weakening is unremarkable, and sufficiently simple
that Agsy, Agda's automatic proof-finder, was able to fill in all of
the code; we include it in the artifact and elide all but the type
signature from the paper.

\AgdaHide{
\begin{code}
lift-var : ∀ {Γ A} T Δ → A ∈ (Δ ++ Γ) → A ∈ (Δ ++ (T :: Γ))
lift-var T ε v = pop v
lift-var T (A :: Δ) top = top
lift-var T (x :: Δ) (pop v) = pop (lift-var T Δ v)
\end{code}
}

\begin{code}
lift-tm
  : ∀ {Γ A} T Δ → (Δ ++ Γ) ⊢ A → (Δ ++ (T :: Γ)) ⊢ A
\end{code}
\AgdaHide{
\begin{code}
lift-tm T Δ (var x) = var (lift-var T Δ x)
lift-tm T Δ <> = <>
lift-tm T Δ (a , b) = lift-tm T Δ a , lift-tm T Δ b
lift-tm T Δ (‘⊥’-elim t) = ‘⊥’-elim (lift-tm T Δ t)
lift-tm T Δ (π₁ t) = π₁ (lift-tm T Δ t)
lift-tm T Δ (π₂ t) = π₂ (lift-tm T Δ t)
lift-tm T Δ (‘λ’ t) = ‘λ’ (lift-tm T (_ :: Δ) t)
lift-tm T Δ (t ‘’ₐ t₁) = lift-tm T Δ t ‘’ₐ lift-tm T Δ t₁
lift-tm T Δ ⌜ t ⌝ = ⌜ t ⌝
lift-tm T Δ (repr t) = repr (lift-tm T Δ t)
lift-tm T Δ (dist t t₁) = dist (lift-tm T Δ t) (lift-tm T Δ t₁)
lift-tm T Δ (Lӧb t) = Lӧb (lift-tm T Δ t)
\end{code}
}

Weakening is a special case of \mintinline{Agda}|lift-tm|.

\begin{code}
wk : ∀ {Γ A B} → Γ ⊢ A → (B :: Γ) ⊢ A
wk = lift-tm _ ε
\end{code}

Finally, we define function composition for our internal language.

\begin{code}
infixl 10 _∘'_
_∘'_ : ∀ {Γ A B C}
  → Γ ⊢ (B ‘→’ C)
  → Γ ⊢ (A ‘→’ B)
  → Γ ⊢ (A ‘→’ C)
f ∘' g = ‘λ’ (wk f ‘’ₐ (wk g ‘’ₐ var top))
\end{code}

Now we are ready to prove that FairBot cooperates with itself.
Sadly, our type system isn't expressive enough to give a general type of bots, but we can still prove things about the interactions of particular bots if we substitute their types by hand.
For example, we can state the desired theorem (that FairBot cooperates with itself) as:

\begin{code}
distf : ∀ {Γ Δ A B}
  → Γ ⊢ (Δ ‘⊢’ A ‘→’ B)
  → Γ ⊢ (Δ ‘⊢’ A) ‘→’ (Δ ‘⊢’ B)
distf bf = ‘λ’ (dist (wk bf) (var top))

evf : ∀ {Γ Δ A}
  → Γ ⊢ (Δ ‘⊢’ A) ‘→’ (Δ ‘⊢’ (Δ ‘⊢’ A))
evf = ‘λ’ (repr (var top))

fb-fb-cooperate : ∀ {Γ A B}
  → Γ ⊢ (Γ ‘⊢’ A) ‘→’ B
  → Γ ⊢(Γ ‘⊢’ B) ‘→’ A
  → Γ ⊢ (A ‘×’ B)
fb-fb-cooperate a b
  =   lӧb (b ∘' distf ⌜ a ⌝ ∘' evf)
    , lӧb (a ∘' distf ⌜ b ⌝ ∘' evf)
\end{code}

We can also state the theorem in a more familiar form with a couple abbreviations

\begin{code}
‘□’ = _‘⊢’_ ε
□ = _⊢_ ε

fb-fb-cooperate' : ∀ {A B}
  → □ (‘□’ A ‘→’ B)
  → □ (‘□’ B ‘→’ A)
  → □ (A ‘×’ B)
fb-fb-cooperate' = fb-fb-cooperate
\end{code}

In the file \texttt{fair-bot-self-cooperates.lagda} in the artifact, we show all the meta-theoretic properties we had before: soundness, inhabitedness, and incompleteness.
\AgdaHide{
We can show inhabitedness immediately in several different ways. We'll take the easiest one.

\begin{code}
inhabited : Σ Type (λ T → ε ⊢ T)
inhabited = ‘⊤’ , <>
\end{code}

We now prove soundness and incompleteness of this system,
and give it a semantic model via an interpretation function.

First, we'll first need to give the standard interpretation.
Again, the simplicity of our system makes our lives easier.
We define the interpreter for types as follows:

\begin{code}
⟦_⟧ᵀ : Type → Set
⟦ Δ ‘⊢’ T ⟧ᵀ = Δ ⊢ T
⟦ A ‘→’ B ⟧ᵀ = ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ
⟦ A ‘×’ B ⟧ᵀ = ⟦ A ⟧ᵀ × ⟦ B ⟧ᵀ
⟦ ‘⊥’ ⟧ᵀ = ⊥
⟦ ‘⊤’ ⟧ᵀ = ⊤
\end{code}

The interpreter for contexts is simplified - we only need simple products to interpret simple contexts.

\begin{code}
⟦_⟧ᶜ : Context → Set
⟦ ε ⟧ᶜ = ⊤
⟦ x :: Γ ⟧ᶜ = ⟦ Γ ⟧ᶜ × ⟦ x ⟧ᵀ
\end{code}

We can then interpret variables in any interpretable context.

\begin{code}
⟦_⟧v : ∀ {Γ A} → A ∈ Γ → ⟦ Γ ⟧ᶜ → ⟦ A ⟧ᵀ
⟦ top ⟧v = snd
⟦ pop v ⟧v = ⟦ v ⟧v ∘ fst
\end{code}

And now we can interpret terms.

\begin{code}
⟦_⟧ᵗ : ∀ {Γ A} → Γ ⊢ A → ⟦ Γ ⟧ᶜ → ⟦ A ⟧ᵀ
⟦ var v ⟧ᵗ = ⟦ v ⟧v
⟦ <> ⟧ᵗ = ᵏ _
⟦ a , b ⟧ᵗ = ᵏ _,_ ˢ ⟦ a ⟧ᵗ ˢ ⟦ b ⟧ᵗ
⟦ ‘⊥’-elim t ⟧ᵗ = ᵏ (λ ()) ˢ ⟦ t ⟧ᵗ
⟦ π₁ t ⟧ᵗ = ᵏ fst ˢ ⟦ t ⟧ᵗ
⟦ π₂ t ⟧ᵗ = ᵏ snd ˢ ⟦ t ⟧ᵗ
⟦ ‘λ’ b ⟧ᵗ = ^ ⟦ b ⟧ᵗ
⟦ f ‘’ₐ x ⟧ᵗ = ⟦ f ⟧ᵗ ˢ ⟦ x ⟧ᵗ
⟦ ⌜ t ⌝ ⟧ᵗ = ᵏ t
⟦ repr t ⟧ᵗ = ᵏ ⌜_⌝ ˢ ⟦ t ⟧ᵗ
⟦ dist f x ⟧ᵗ = ᵏ _‘’ₐ_ ˢ ⟦ f ⟧ᵗ ˢ ⟦ x ⟧ᵗ
⟦ Lӧb l ⟧ᵗ = ᵏ lӧb ˢ ⟦ l ⟧ᵗ
\end{code}

Which lets us prove all our sanity checks.

\begin{code}
‘¬’_ : Type → Type
‘¬’ T = T ‘→’ ‘⊥’

consistency : ¬ (□ ‘⊥’)
consistency f = ⟦ f ⟧ᵗ tt

incompleteness : ¬ (□ (‘¬’ ‘□’ ‘⊥’))
incompleteness t = ⟦ lӧb t ⟧ᵗ tt

soundness : ∀ {A} → □ A → ⟦ A ⟧ᵀ
soundness a = ⟦ a ⟧ᵗ tt
\end{code}

}
