 \documentclass[preprint]{sigplanconf}

 \usepackage{agda}

 % The following packages are needed because unicode
 % is translated (using the next set of packages) to
 % latex commands. You may need more packages if you
 % use more unicode characters:

 \usepackage{amssymb}
 \usepackage{amsmath}
 \usepackage{hyperref}
 \usepackage{xcolor}
 \usepackage{minted}
 \usepackage{upquote}
 % \usepackage{bbm}
 % \usepackage[greek,english]{babel}

 % disable minted red error boxes on syntax error
 \makeatletter
 \expandafter\def\csname PYGdefault@tok@err\endcsname{\def\PYGdefault@bc##1{{\strut ##1}}}
 \makeatother

 % This handles the translation of unicode to latex:

 \usepackage{ucs}
 \usepackage[utf8x]{inputenc}
 % \usepackage{autofe}

 % Some characters that are not automatically defined
 % (you figure out by the latex compilation errors you get),
 % and you need to define:

 \DeclareUnicodeCharacter{8988}{\ensuremath{\ulcorner}}
 \DeclareUnicodeCharacter{8989}{\ensuremath{\urcorner}}
 \DeclareUnicodeCharacter{8990}{\ensuremath{\llcorner}}
 \DeclareUnicodeCharacter{8991}{\ensuremath{\lrcorner}}
 \DeclareUnicodeCharacter{9633}{\ensuremath{\square}}
 \DeclareUnicodeCharacter{931}{\ensuremath{\Sigma}}
 \DeclareUnicodeCharacter{915}{\ensuremath{\Gamma}}
 \DeclareUnicodeCharacter{928}{\ensuremath{\Pi}}
 \DeclareUnicodeCharacter{8803}{\ensuremath{\overline{\equiv}}}
 \DeclareUnicodeCharacter{9659}{\ensuremath{\triangleright}}
 \DeclareUnicodeCharacter{1255}{\"o}
 \DeclareUnicodeCharacter{8336}{\ensuremath{{}_a}}
 \DeclareUnicodeCharacter{8216}{\text{\textquoteleft}}
 \DeclareUnicodeCharacter{8217}{\text{\textquoteright}}

 % Add more as you need them (shouldn’t happen often).

\newcommand{\todo}[1]{\textcolor{red}{TODO: #1}}

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\conferenceinfo{ICFP '16}{September 19--21, 2016, Nara, Japan}
\copyrightyear{2016}
%\copyrightdata{978-1-nnnn-nnnn-n/yy/mm}
%\copyrightdoi{nnnnnnn.nnnnnnn}

% Uncomment the publication rights you want to use.
%\publicationrights{transferred}
\publicationrights{licensed}     % this is the default
%\publicationrights{author-pays}

%\titlebanner{banner above paper title}        % These are ignored unless
%\preprintfooter{short description of paper}   % 'preprint' option specified.

\title{L\"ob's Theorem}
\subtitle{A functional pearl of dependently typed quining}

\authorinfo{Name1}
           {Affiliation1}
           {Email1}
\authorinfo{Name2\and Name3}
           {Affiliation2/3}
           {Email2/3}

\maketitle

 \AgdaHide{
  \begin{code}
module lob where
  \end{code}
}

\category{CR-number}{subcategory}{third-level}

% general terms are not compulsory anymore,
% you may leave them out
\terms
Agda, Lob, quine, self-reference

\keywords
Agda, Lob, quine, self-reference

\begin{abstract}
This is the text of the abstract.
\end{abstract}

\begin{quotation}
\noindent \textit{If P's answer is `Bad!', Q will suddenly stop. \\
But otherwise, Q will go back to the top, \\
and start off again, looping endlessly back, \\
till the universe dies and turns frozen and black.}
\end{quotation}
\begin{flushright}
Excerpt from \emph{Scooping the Loop Snooper}, by Geoffrey K.~Pullum (\url{http://www.lel.ed.ac.uk/~gpullum/loopsnoop.html}\cite{})
\end{flushright}

\section{TODO}
  - cite Using Reflection to Explain and Enhance Type Theory?


\section{Introduction}
 L\"ob's thereom has a variety of applications, from proving incompleteness of a logical theory as a trivial corrolary, to acting as a no-go theorem for a large class of self-interpreters (\todo{mention F$_omega$?}), from allowing robust cooperation in the Prisoner's Dilemma with Source Code~\cite{}, to curing social anxiety~\cite{}.

 ``What is L\"ob's theorem, this versatile tool with wonderous applications?'' you may ask.

 Consider the sentence ``if this sentence is true, then you, dear reader, are the most awesome person in the world.''  Suppose that this sentence is true.  Then you, dear reader are the most awesome person in the world.  Since this is exactly what the sentence asserts, the sentence is true, and you, dear reader, are the most awesome person in the world.  For those more comfortable with symbolic logic, we can let $X$ be the statement ``you, dear reader, are the most awesome person in the world'', and we can let $A$ be the statement ``if this sentence is true, then $X$''.  Since we have that $A$ and $A → B$ are the same, if we assume $A$, we are also assuming $A → B$, and hence we have $B$, and since assuming $A$ yields $B$, we have that $A → B$.  What went wrong?\footnote{Those unfamiliar with conditionals should note that the ``if \ldots\space then \ldots'' we use here is the logical ``if'', where ``if false then $X$'' is always true, and not the counterfactual ``if''.}

 It can be made quite clear that something is wrong; the more common form of this sentence is used to prove the existence of Santa Claus to logical children: considering the sentence ``if this sentence is true, then Santa Claus exists'', we can prove that Santa Claus exists.  By the same logic, though, we can prove that Santa Claus does not exist by considering the sentence ``if this sentence is true, then Santa Claus does not exist.''  Whether you consider it absurd that Santa Claus exist, or absurd that Santa Claus not exist, surely you will consider it absurd that Santa Claus both exist and not exist.  This is known as Curry's paradox.

 Have you figured out what went wrong?

 The sentence that we have been considering is not a valid mathematical sentence.  Ask yourself what makes it invalid, while we consider a similar sentence that is actually valid.

 Now consider the sentence``if this sentence is provable, then you, dear reader, are the most awesome person in the world.''  Fix a particular formalization of provability (for example, Peano Arithmetic, or Martin--L\"of Type Theory).  To prove that this sentence is true, suppose that it is provable.  We must now show that you, dear reader, are the most awesome person in the world.  \emph{If provability implies truth}, then the sentence is true, and then you, dear reader, are the most awesome person in the world.  Thus, if we can assume that provability implies truth, then we can prove that the sentence is true.  This, in a nutshell, is L\"ob's theorem: to prove $X$, it suffices to prove that $X$ is true whenever $X$ is provable.  Symbolically, this is
$$□ (□ X -> X) → □ X$$
where $□ X$ means ``$X$ is provable'' (in our fixed formalization of provability).

 Let us now return to the question we posed above: what went wrong with our original sentence?  The answer is that self-reference with truth is impossible, and the clearest way I know to argue for this is via the Curry--Howard Isomorphism; in a particular technical sense, the problem is that self-reference with truth fails to terminate.

 The Curry--Howard Isomorphism establishes an equivalence between types and propositions, between (well-typed, terminating, functional) programs and proofs.  See Table\ref{} for some examples.  Now we ask: what corresponds to a formalization of provability?  If a proof of P is a terminating functional program which is well-typed at the type corresponding to P, and to assert that P is provable is to assert that the type corresponding to P is inhabited, then an encoding of a proof is an encoding of a program.  Although mathematicians typically use G\"odel codes to encode propositions and proofs, a more natural choice of encoding programs will be abstract syntax trees.  In particular, a valid syntactic proof of a given (syntactic) proposition corresponds to a well-typed syntax tree for an inhabitant of the corresponding syntactic type.

 TODO: Table of CH-Equivalence: Type<->set of proofs<->Proposition, Term/(Terminating, Well-typed, functional) Program<->Proof, Function Type<->set of functions<->Implication, Pairing<->cartesian product<->Conjunction, Sum Type<->disjoint union<->disjunction

 Unless otherwise specified, we will henceforth consider only well-typed, terminating programs; when we say "program", the adjectives "well-typed" and "terminating" are implied.

 Before diving into L\"ob's theorem in detail, we'll first visit a standard paradigm for formalizing the syntax of dependent type theory. (TODO: Move this?)

\section{Quines}
 What is the computational equivalent of the sentence ``If this sentence is provable, then $X$''?  It will be something of the form ``??? → $X$''.  As a warm-up, let's look at a Python program that returns a string representation of this type.

 To do this, we need a program that outputs its own source code.  There are three genuinely distinct solutions, the first of which is degenerate, and the second of which is cheeky (or sassy?).  These ``cheating'' solutions are:
 \begin{itemize}
   \item The empty program, which outputs nothing.
   \item The program \mintinline{python}|print(open(__file__, 'r').read())|, which relies on the Python interpreter to get the source code of the program.
 \end{itemize}

 Now we develop the standard solution.  At a first gloss, it looks like:
\begin{minted}[mathescape,
%               numbersep=5pt,
               gobble=2,
%               frame=lines,
%               framesep=2mm%
]{python}
  (lambda my_type: '(' + my_type + ') -> X') "???"
\end{minted}

 Now we need to replace \mintinline{python}|"???"| with the entirety of this program code.  We use Python's string escaping function (\mintinline{python}|repr|) and replacement syntax (\mintinline{python}|"foo %s bar" % "baz"| becomes \mintinline{python}|"foo baz bar"|):

\begin{minted}[gobble=2]{python}
  (lambda my_type: '(' + my_type % repr(my_type) + ') → X')
    ("(lambda my_type: '(' + my_type %% repr(my_type) + ') → X')\n  (%s)")
\end{minted}
 This is a slight modification on the standard way of programming a quine, a program that outputs its own source-code.
 Suppose we have a function □ that takes in a string representation of a type, and returns the type of syntax trees of programs producing that type.  Then our L\"obian sentence would look something like (if → were valid notation for function types in Python)
\begin{minted}[gobble=1]{python}
 (lambda my_type: □ (my_type % repr(my_type)) → X)
   ("(lambda my_type: □ (my_type %% repr(my_type)) → X)\n  (%s)")
\end{minted}
 Now, finally, we can see what goes wrong when we consider using "if this sentence is true" rather than ``if this sentence is provable''.  Provability corresponds to syntax trees for programs; truth corresponds to execution of the program itself.  Our pseudo-Python thus becomes
\begin{minted}[gobble=1]{python}
 (lambda my_type: eval(my_type % repr(my_type)) → X)
   ("(lambda my_type: eval(my_type %% repr(my_type)) → X)\n  (%s)")
\end{minted}

 This code never terminates!  So, in a quite literal sense, the issue with our original sentence was that, if we tried to phrase it, we'd never finish.

 Note well that the type (□ X → X) is a type that takes syntax trees and evaluates them; it is the type of an interpreter.  (\todo{maybe move this sentence?})

\section{Abstract Syntax Trees for Dependent Type Theory}

  The idea of formalizing a type of syntax trees which only permits well-typed programs is common in the literature.  (TODO: citations)  For example, here is a very simple (and incomplete) formalization with $\Pi$, a unit type (⊤), an empty type (⊥), and lambdas.  (FIXME: What's the right level of simplicity?)

  We begin with some standard data type declarations.

\begin{code}
open import Agda.Primitive public
  using    (Level; _⊔_; lzero; lsuc)

infixl 1 _,_
infixr 2 _×_
infixl 1 _≡_

record ⊤ {ℓ} : Set ℓ where
  constructor tt

data ⊥ {ℓ} : Set ℓ where

record Σ {ℓ ℓ′} (A : Set ℓ) (P : A → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : P proj₁

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

transport : ∀ {A : Set} {x : A} {y : A} → (P : A → Set) → x ≡ y → P x → P y
transport P refl v = v
\end{code}

\AgdaHide{
  \begin{code}
module dependent-type-theory where
  \end{code}
}


 \begin{code}
  mutual
   infixl 2 _▻_

   data Context : Set where
    ε : Context
    _▻_ : (Γ : Context) → Type Γ → Context

   data Type : Context → Set where
    ‘⊤’ : ∀ {Γ} → Type Γ
    ‘⊥’ : ∀ {Γ} → Type Γ
    ‘Π’ : ∀ {Γ} → (A : Type Γ) → Type (Γ ▻ A) → Type Γ

   data Term : {Γ : Context} → Type Γ  → Set where
    ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
    ‘λ’ : ∀ {Γ A B} → Term {Γ ▻ A} B → Term {Γ} (‘Π’ A B)
 \end{code}

  An easy way to check consistency of a syntactic theory which is weaker than the theory of the ambient proof assistant is to define an interpretation function, also commonly known as an unquoter, or a denotation function, from the syntax into the universe of types.  Here is an example of such a function:

\begin{code}
  mutual
   ⌞_⌟c : Context → Set
   ⌞ ε ⌟c = ⊤
   ⌞ Γ ▻ T ⌟c = Σ ⌞ Γ ⌟c ⌞ T ⌟T

   ⌞_⌟T : ∀ {Γ} → Type Γ → ⌞ Γ ⌟c → Set
   ⌞ ‘⊤’ ⌟T ⌞Γ⌟ = ⊤
   ⌞ ‘⊥’ ⌟T ⌞Γ⌟ = ⊥
   ⌞ ‘Π’ A B ⌟T ⌞Γ⌟ = (x : ⌞ A ⌟T ⌞Γ⌟) → ⌞ B ⌟T (⌞Γ⌟ , x)

   ⌞_⌟t : ∀ {Γ} {T : Type Γ} → Term T → (⌞Γ⌟ : ⌞ Γ ⌟c) → ⌞ T ⌟T ⌞Γ⌟
   ⌞ ‘tt’ ⌟t ⌞Γ⌟ = tt
   ⌞ (‘λ’ f) ⌟t ⌞Γ⌟ x = ⌞ f ⌟t (⌞Γ⌟ , x)
\end{code}

\section{This Paper}
 In this paper, we make extensive use of this trick for validating models.  We formalize the simplest syntax that supports L\"ob's theorem and prove it sound relative to Agda in 13 lines of code; the understanding is that this syntax could be extended to support basically anything you might want.  We then present an extended version of this solution, which supports enough operations that we can prove our syntax sound (consistent), incomplete, and nonempty.  In a hundred lines of code, we prove L\"ob's theorem under the assumption that we are given a quine; this is basically the well-typed functional version of the program that uses \verb|open(__file__, 'r').read()|.  Finally, we sketch our implementation of L\"ob's theorem (code in an appendix) based on the assumption only that we can add a level of quotation to our syntax tree; this is the equivalent of letting the compiler implement \verb|repr()|, rather than implementing it ourselves.  We close with an application to the prisoner's dilemma, as well as some discussion about avenues for removing the hard-coded \verb|repr|.

\section{Prior Work}
  \todo{Use of L\"ob's theorem in program logic as an induction principle? (TODO)}

  \todo{Brief mention of Lob's theorem in Haskell / elsewhere / ? (TODO)}

\section{Trivial Encoding}
\AgdaHide{
  \begin{code}
module trivial-encoding where
  \end{code}
}

\begin{code}
 infixr 1 _‘→’_

 data Type : Set where
   _‘→’_ : Type → Type → Type
   ‘□’ : Type → Type

 data □ : Type → Set where
   Lӧb : ∀ {X} → □ (‘□’ X ‘→’ X) → □ X

 ⌞_⌟ : Type → Set
 ⌞ A ‘→’ B ⌟ = ⌞ A ⌟ → ⌞ B ⌟
 ⌞ ‘□’ T ⌟   = □ T

 ⌞_⌟t : ∀ {T : Type} → □ T → ⌞ T ⌟
 ⌞ (Lӧb □‘X’→X) ⌟t = ⌞ □‘X’→X ⌟t (Lӧb □‘X’→X)

 lӧb : ∀ {‘X’} → □ (‘□’ ‘X’ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
 lӧb f = ⌞ Lӧb f ⌟t

\end{code}

\section{Encoding with Soundness, Incompleteness, and Non-Emptyness}

\AgdaHide{
  \begin{code}
module sound-incomplete-nonempty where
  \end{code}
}

\begin{code}
 infixr 1 _‘→’_

 mutual
   data Type : Set where
     _‘→’_ : Type → Type → Type
     ‘□’ : Type → Type
     ‘⊤’ : Type
     ‘⊥’ : Type

   data □ : Type → Set where
     Lӧb : ∀ {X} → □ (‘□’ X ‘→’ X) → □ X
     ‘tt’ : □ ‘⊤’

 mutual
   ⌞_⌟ : Type → Set
   ⌞ A ‘→’ B ⌟ = ⌞ A ⌟ → ⌞ B ⌟
   ⌞ ‘□’ T ⌟   = □ T
   ⌞ ‘⊤’ ⌟     = ⊤
   ⌞ ‘⊥’ ⌟     = ⊥

   ⌞_⌟t : ∀ {T : Type} → □ T → ⌞ T ⌟
   ⌞ (Lӧb □‘X’→X) ⌟t = ⌞ □‘X’→X ⌟t (Lӧb □‘X’→X)
   ⌞ ‘tt’ ⌟t = tt

 ¬_ : Set → Set
 ¬ T = T → ⊥

 ‘¬’_ : Type → Type
 ‘¬’ T = T ‘→’ ‘⊥’

 lӧb : ∀ {‘X’} → □ (‘□’ ‘X’ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
 lӧb f = ⌞ Lӧb f ⌟t

 incompleteness : ¬ □ (‘¬’ (‘□’ ‘⊥’))
 incompleteness = lӧb

 soundness : ¬ □ ‘⊥’
 soundness x = ⌞ x ⌟t

 non-emptyness : □ ‘⊤’
 non-emptyness = ‘tt’
\end{code}

\section{Encoding with Quines}
\begin{code}
module lob-by-quines where
 infixl 2 _▻_
 infixl 3 _‘’_
 infixr 1 _‘→’_
 infixl 3 _‘’ₐ_
 infixl 3 _w‘‘’’ₐ_
 infixr 2 _‘∘’_

 mutual
   data Context : Set where
     ε : Context
     _▻_ : (Γ : Context) → Type Γ → Context

   data Type : Context → Set where
     W : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
     W1 : ∀ {Γ A B} → Type (Γ ▻ B) → Type (Γ ▻ A ▻ (W {Γ = Γ} {A = A} B))
     _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
     ‘Typeε’ : ∀ {Γ} → Type Γ
     ‘□’ : ∀ {Γ} → Type (Γ ▻ ‘Typeε’)
     _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
     Quine : Type (ε ▻ ‘Typeε’) → Type ε
     ‘⊤’ : ∀ {Γ} → Type Γ
     ‘⊥’ : ∀ {Γ} → Type Γ

   data Term : {Γ : Context} → Type Γ → Set where
     ⌜_⌝ : ∀ {Γ} → Type ε → Term {Γ} ‘Typeε’
     ⌜_⌝t : ∀ {Γ T} → Term {ε} T → Term {Γ} (‘□’ ‘’ ⌜ T ⌝)
     ‘⌜‘VAR₀’⌝t’ : ∀ {T} → Term {ε ▻ ‘□’ ‘’ ⌜ T ⌝} (W (‘□’ ‘’ ⌜ ‘□’ ‘’ ⌜ T ⌝ ⌝))
     ‘λ∙’ : ∀ {Γ A B} → Term {Γ ▻ A} (W B) → Term {Γ} (A ‘→’ B)
     ‘VAR₀’ : ∀ {Γ T} → Term {Γ ▻ T} (W T)
     _‘’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
     quine→ : ∀ {φ} → Term {ε} (Quine φ        ‘→’ φ ‘’ ⌜ Quine φ ⌝)
     quine← : ∀ {φ} → Term {ε} (φ ‘’ ⌜ Quine φ ⌝ ‘→’ Quine φ)
     ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
     →SW1SV→W : ∀ {Γ T X A B} {x : Term X}
       → Term {Γ} (T ‘→’ (W1 A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x)
       → Term {Γ} (T ‘→’ A ‘’ x ‘→’ B)
     ←SW1SV→W : ∀ {Γ T X A B} {x : Term X}
       → Term {Γ} ((W1 A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x ‘→’ T)
       → Term {Γ} ((A ‘’ x ‘→’ B) ‘→’ T)
     w : ∀ {Γ A T} → Term {Γ} A → Term {Γ ▻ T} (W A)
     w→ : ∀ {Γ A B X} → Term {Γ} (A ‘→’ B) → Term {Γ ▻ X} (W A ‘→’ W B)
     _‘∘’_ : ∀ {Γ A B C} → Term {Γ} (B ‘→’ C) → Term {Γ} (A ‘→’ B) → Term {Γ} (A ‘→’ C)
     _w‘‘’’ₐ_ : ∀ {A B T} → Term {ε ▻ T} (W (‘□’ ‘’ ⌜ A ‘→’ B ⌝)) → Term {ε ▻ T} (W (‘□’ ‘’ ⌜ A ⌝)) → Term {ε ▻ T} (W (‘□’ ‘’ ⌜ B ⌝))


 □ : Type ε → Set _
 □ = Term {ε}

 max-level : Level
 max-level = lzero

 mutual
   Context⇓ : (Γ : Context) → Set (lsuc max-level)
   Context⇓ ε = ⊤
   Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (Type⇓ {Γ} T)

   Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set max-level
   Type⇓ (W T) Γ⇓ = Type⇓ T (Σ.proj₁ Γ⇓)
   Type⇓ (W1 T) Γ⇓ = Type⇓ T ((Σ.proj₁ (Σ.proj₁ Γ⇓)) , (Σ.proj₂ Γ⇓))
   Type⇓ (T ‘’ x) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ x Γ⇓)
   Type⇓ ‘Typeε’ Γ⇓ = Lifted (Type ε)
   Type⇓ ‘□’ Γ⇓ = Lifted (Term {ε} (lower (Σ.proj₂ Γ⇓)))
   Type⇓ (A ‘→’ B) Γ⇓ = Type⇓ A Γ⇓ → Type⇓ B Γ⇓
   Type⇓ ‘⊤’ Γ⇓ = ⊤
   Type⇓ ‘⊥’ Γ⇓ = ⊥
   Type⇓ (Quine φ) Γ⇓ = Type⇓ φ (Γ⇓ , (lift (Quine φ)))

   Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓
   Term⇓ ⌜ x ⌝ Γ⇓ = lift x
   Term⇓ ⌜ x ⌝t Γ⇓ = lift x
   Term⇓ ‘⌜‘VAR₀’⌝t’ Γ⇓ = lift ⌜ (lower (Σ.proj₂ Γ⇓)) ⌝t
   Term⇓ (f ‘’ₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
   Term⇓ ‘tt’ Γ⇓ = tt
   Term⇓ (quine→ {φ}) Γ⇓ x = x
   Term⇓ (quine← {φ}) Γ⇓ x = x
   Term⇓ (‘λ∙’ f) Γ⇓ x = Term⇓ f (Γ⇓ , x)
   Term⇓ ‘VAR₀’ Γ⇓ = Σ.proj₂ Γ⇓
   Term⇓ (←SW1SV→W f) = Term⇓ f
   Term⇓ (→SW1SV→W f) = Term⇓ f
   Term⇓ (w x) Γ⇓ = Term⇓ x (Σ.proj₁ Γ⇓)
   Term⇓ (w→ f) Γ⇓ = Term⇓ f (Σ.proj₁ Γ⇓)
   Term⇓ (g ‘∘’ f) Γ⇓ x = Term⇓ g Γ⇓ (Term⇓ f Γ⇓ x)
   Term⇓ (f w‘‘’’ₐ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘’ₐ lower (Term⇓ x Γ⇓))

 module inner (‘X’ : Type ε) (‘f’ : Term {ε} (‘□’ ‘’ ⌜ ‘X’ ⌝ ‘→’ ‘X’)) where
   ‘H’ : Type ε
   ‘H’ = Quine (W1 ‘□’ ‘’ ‘VAR₀’ ‘→’ W ‘X’)

   ‘toH’ : □ ((‘□’ ‘’ ⌜ ‘H’ ⌝ ‘→’ ‘X’) ‘→’ ‘H’)
   ‘toH’ = ←SW1SV→W quine←

   ‘fromH’ : □ (‘H’ ‘→’ (‘□’ ‘’ ⌜ ‘H’ ⌝ ‘→’ ‘X’))
   ‘fromH’ = →SW1SV→W quine→

   ‘□‘H’→□‘X’’ : □ (‘□’ ‘’ ⌜ ‘H’ ⌝ ‘→’ ‘□’ ‘’ ⌜ ‘X’ ⌝)
   ‘□‘H’→□‘X’’ = ‘λ∙’ (w ⌜ ‘fromH’ ⌝t w‘‘’’ₐ ‘VAR₀’ w‘‘’’ₐ ‘⌜‘VAR₀’⌝t’)

   ‘h’ : Term ‘H’
   ‘h’ = ‘toH’ ‘’ₐ (‘f’ ‘∘’ ‘□‘H’→□‘X’’)

   Lӧb : □ ‘X’
   Lӧb = ‘fromH’ ‘’ₐ ‘h’ ‘’ₐ ⌜ ‘h’ ⌝t

 Lӧb : ∀ {X} → Term {ε} (‘□’ ‘’ ⌜ X ⌝ ‘→’ X) → Term {ε} X
 Lӧb {X} f = inner.Lӧb X f

 ⌞_⌟ : Type ε → Set _
 ⌞ T ⌟ = Type⇓ T tt

 ‘¬’_ : ∀ {Γ} → Type Γ → Type Γ
 ‘¬’ T = T ‘→’ ‘⊥’

 lӧb : ∀ {‘X’} → □ (‘□’ ‘’ ⌜ ‘X’ ⌝ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
 lӧb f = Term⇓ (Lӧb f) tt

 ¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
 ¬_ {ℓ} T = T → ⊥ {ℓ}

 incompleteness : ¬ □ (‘¬’ (‘□’ ‘’ ⌜ ‘⊥’ ⌝))
 incompleteness = lӧb

 soundness : ¬ □ ‘⊥’
 soundness x = Term⇓ x tt

 non-emptyness : Σ (Type ε) (λ T → □ T)
 non-emptyness = ‘⊤’ , ‘tt’

\end{code}

\section{Digression: Application of Quining to The Prisoner's Dilemma}

\begin{code}
module prisoners-dilemma where

 module lob where
   infixl 2 _▻_
   infixl 3 _‘’_
   infixr 1 _‘→’_
   infixr 1 _‘‘→’’_
   infixr 1 _ww‘‘‘→’’’_
   infixl 3 _‘’ₐ_
   infixl 3 _w‘‘’’ₐ_
   infixr 2 _‘∘’_
   infixr 2 _‘×’_
   infixr 2 _‘‘×’’_
   infixr 2 _w‘‘×’’_

   mutual
     data Context : Set where
       ε : Context
       _▻_ : (Γ : Context) → Type Γ → Context

     data Type : Context → Set where
       W : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
       W1 : ∀ {Γ A B} → Type (Γ ▻ B) → Type (Γ ▻ A ▻ (W {Γ = Γ} {A = A} B))
       _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
       ‘Type’ : ∀ Γ → Type Γ
       ‘Term’ : ∀ {Γ} → Type (Γ ▻ ‘Type’ Γ)
       _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
       _‘×’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
       Quine : ∀ {Γ} → Type (Γ ▻ ‘Type’ Γ) → Type Γ
       ‘⊤’ : ∀ {Γ} → Type Γ
       ‘⊥’ : ∀ {Γ} → Type Γ

     data Term : {Γ : Context} → Type Γ → Set where
       ⌜_⌝ : ∀ {Γ} → Type Γ → Term {Γ} (‘Type’ Γ)
       ⌜_⌝t : ∀ {Γ T} → Term {Γ} T → Term {Γ} (‘Term’ ‘’ ⌜ T ⌝)
       ‘⌜‘VAR₀’⌝t’ : ∀ {Γ T} → Term {Γ ▻ ‘Term’ ‘’ ⌜ T ⌝} (W (‘Term’ ‘’ ⌜ ‘Term’ ‘’ ⌜ T ⌝ ⌝))
       ‘⌜‘VAR₀’⌝’ : ∀ {Γ} → Term {Γ ▻ ‘Type’ Γ} (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝))
       ‘λ∙’ : ∀ {Γ A B} → Term {Γ ▻ A} (W B) → Term {Γ} (A ‘→’ B)
       ‘VAR₀’ : ∀ {Γ T} → Term {Γ ▻ T} (W T)
       _‘’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
       ‘‘×'’’ : ∀ {Γ} → Term {Γ} (‘Type’ Γ ‘→’ ‘Type’ Γ ‘→’ ‘Type’ Γ)
       quine→ : ∀ {Γ φ} → Term {Γ} (Quine φ        ‘→’ φ ‘’ ⌜ Quine φ ⌝)
       quine← : ∀ {Γ φ} → Term {Γ} (φ ‘’ ⌜ Quine φ ⌝ ‘→’ Quine φ)
       ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
       SW : ∀ {Γ X A} {a : Term A} → Term {Γ} (W X ‘’ a) → Term X
       →SW1SV→W : ∀ {Γ T X A B} {x : Term X}
         → Term {Γ} (T ‘→’ (W1 A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x)
         → Term {Γ} (T ‘→’ A ‘’ x ‘→’ B)
       ←SW1SV→W : ∀ {Γ T X A B} {x : Term X}
         → Term {Γ} ((W1 A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x ‘→’ T)
         → Term {Γ} ((A ‘’ x ‘→’ B) ‘→’ T)
       →SW1SV→SW1SV→W : ∀ {Γ T X A B} {x : Term X}
         → Term {Γ} (T ‘→’ (W1 A ‘’ ‘VAR₀’ ‘→’ W1 A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x)
         → Term {Γ} (T ‘→’ A ‘’ x ‘→’ A ‘’ x ‘→’ B)
       ←SW1SV→SW1SV→W : ∀ {Γ T X A B} {x : Term X}
         → Term {Γ} ((W1 A ‘’ ‘VAR₀’ ‘→’ W1 A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x ‘→’ T)
         → Term {Γ} ((A ‘’ x ‘→’ A ‘’ x ‘→’ B) ‘→’ T)
       w : ∀ {Γ A T} → Term {Γ} A → Term {Γ ▻ T} (W A)
       w→ : ∀ {Γ A B X} → Term {Γ ▻ X} (W (A ‘→’ B)) → Term {Γ ▻ X} (W A ‘→’ W B)
       →w : ∀ {Γ A B X} → Term {Γ ▻ X} (W A ‘→’ W B) → Term {Γ ▻ X} (W (A ‘→’ B))
       ww→ : ∀ {Γ A B X Y} → Term {Γ ▻ X ▻ Y} (W (W (A ‘→’ B))) → Term {Γ ▻ X ▻ Y} (W (W A) ‘→’ W (W B))
       →ww : ∀ {Γ A B X Y} → Term {Γ ▻ X ▻ Y} (W (W A) ‘→’ W (W B)) → Term {Γ ▻ X ▻ Y} (W (W (A ‘→’ B)))
       _‘∘’_ : ∀ {Γ A B C} → Term {Γ} (B ‘→’ C) → Term {Γ} (A ‘→’ B) → Term {Γ} (A ‘→’ C)
       _w‘‘’’ₐ_ : ∀ {Γ A B T} → Term {Γ ▻ T} (W (‘Term’ ‘’ ⌜ A ‘→’ B ⌝)) → Term {Γ ▻ T} (W (‘Term’ ‘’ ⌜ A ⌝)) → Term {Γ ▻ T} (W (‘Term’ ‘’ ⌜ B ⌝))
       ‘‘’ₐ’ : ∀ {Γ A B} → Term {Γ} (‘Term’ ‘’ ⌜ A ‘→’ B ⌝ ‘→’ ‘Term’ ‘’ ⌜ A ⌝ ‘→’ ‘Term’ ‘’ ⌜ B ⌝)
       -- _w‘‘’’_ : ∀ {Γ A B T} → Term {Γ ▻ T} (‘Type’ (Γ ▻ T)) → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ T ⌝))) → Term {Γ ▻ A ▻ B} (W (W (‘Type’ Γ)))
       ‘‘□’’ : ∀ {Γ A B} → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝))) → Term {Γ ▻ A ▻ B} (W (W (‘Type’ Γ)))
       -- ‘‘’’' : ∀ {Γ A} → Term {Γ ▻ A} (‘Type’ (Γ ▻ A) ‘→’ W (‘Term’ ‘’ ⌜ A ⌝) ‘→’ W (‘Type’ Γ))
       _‘‘→’’_ : ∀ {Γ} → Term {Γ} (‘Type’ Γ) → Term {Γ} (‘Type’ Γ) → Term {Γ} (‘Type’ Γ)
       _ww‘‘‘→’’’_ : ∀ {Γ A B} → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝))) → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝))) → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝)))
       _ww‘‘‘×’’’_ : ∀ {Γ A B} → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝))) → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝))) → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝)))

   □ : Type ε → Set _
   □ = Term {ε}

   ‘□’ : ∀ {Γ} → Type Γ → Type Γ
   ‘□’ T = ‘Term’ ‘’ ⌜ T ⌝

   _‘‘×’’_ : ∀ {Γ} → Term {Γ} (‘Type’ Γ) → Term {Γ} (‘Type’ Γ) → Term {Γ} (‘Type’ Γ)
   A ‘‘×’’ B = ‘‘×'’’ ‘’ₐ A ‘’ₐ B

   max-level : Level
   max-level = lzero

   mutual
     Context⇓ : (Γ : Context) → Set (lsuc max-level)
     Context⇓ ε = ⊤
     Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (Type⇓ {Γ} T)

     Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set max-level
     Type⇓ (W T) Γ⇓ = Type⇓ T (Σ.proj₁ Γ⇓)
     Type⇓ (W1 T) Γ⇓ = Type⇓ T ((Σ.proj₁ (Σ.proj₁ Γ⇓)) , (Σ.proj₂ Γ⇓))
     Type⇓ (T ‘’ x) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ x Γ⇓)
     Type⇓ (‘Type’ Γ) Γ⇓ = Lifted (Type Γ)
     Type⇓ ‘Term’ Γ⇓ = Lifted (Term (lower (Σ.proj₂ Γ⇓)))
     Type⇓ (A ‘→’ B) Γ⇓ = Type⇓ A Γ⇓ → Type⇓ B Γ⇓
     Type⇓ (A ‘×’ B) Γ⇓ = Type⇓ A Γ⇓ × Type⇓ B Γ⇓
     Type⇓ ‘⊤’ Γ⇓ = ⊤
     Type⇓ ‘⊥’ Γ⇓ = ⊥
     Type⇓ (Quine φ) Γ⇓ = Type⇓ φ (Γ⇓ , (lift (Quine φ)))

     Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓
     Term⇓ ⌜ x ⌝ Γ⇓ = lift x
     Term⇓ ⌜ x ⌝t Γ⇓ = lift x
     Term⇓ ‘⌜‘VAR₀’⌝t’ Γ⇓ = lift ⌜ (lower (Σ.proj₂ Γ⇓)) ⌝t
     Term⇓ ‘⌜‘VAR₀’⌝’ Γ⇓ = lift ⌜ (lower (Σ.proj₂ Γ⇓)) ⌝
     Term⇓ (f ‘’ₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
     Term⇓ ‘tt’ Γ⇓ = tt
     Term⇓ (quine→ {φ}) Γ⇓ x = x
     Term⇓ (quine← {φ}) Γ⇓ x = x
     Term⇓ (‘λ∙’ f) Γ⇓ x = Term⇓ f (Γ⇓ , x)
     Term⇓ ‘VAR₀’ Γ⇓ = Σ.proj₂ Γ⇓
     Term⇓ (SW t) = Term⇓ t
     Term⇓ (←SW1SV→W f) = Term⇓ f
     Term⇓ (→SW1SV→W f) = Term⇓ f
     Term⇓ (←SW1SV→SW1SV→W f) = Term⇓ f
     Term⇓ (→SW1SV→SW1SV→W f) = Term⇓ f
     Term⇓ (w x) Γ⇓ = Term⇓ x (Σ.proj₁ Γ⇓)
     Term⇓ (w→ f) Γ⇓ = Term⇓ f Γ⇓
     Term⇓ (→w f) Γ⇓ = Term⇓ f Γ⇓
     Term⇓ (ww→ f) Γ⇓ = Term⇓ f Γ⇓
     Term⇓ (→ww f) Γ⇓ = Term⇓ f Γ⇓
     Term⇓ ‘‘×'’’ Γ⇓ A B = lift (lower A ‘×’ lower B)
     Term⇓ (g ‘∘’ f) Γ⇓ x = Term⇓ g Γ⇓ (Term⇓ f Γ⇓ x)
     Term⇓ (f w‘‘’’ₐ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘’ₐ lower (Term⇓ x Γ⇓))
     Term⇓ ‘‘’ₐ’ Γ⇓ f x = lift (lower f ‘’ₐ lower x)
     -- Term⇓ (f w‘‘’’ x) Γ⇓ = lift {!!} --(lower (Term⇓ f Γ⇓) ‘’ lower (Term⇓ x Γ⇓))
     Term⇓ (‘‘□’’ {Γ} T) Γ⇓ = lift (‘Term’ ‘’ lower (Term⇓ T Γ⇓))
     Term⇓ (A ‘‘→’’ B) Γ⇓ = lift ((lower (Term⇓ A Γ⇓)) ‘→’ (lower (Term⇓ B Γ⇓)))
     Term⇓ (A ww‘‘‘→’’’ B) Γ⇓ = lift ((lower (Term⇓ A Γ⇓)) ‘‘→’’ (lower (Term⇓ B Γ⇓)))
     Term⇓ (A ww‘‘‘×’’’ B) Γ⇓ = lift ((lower (Term⇓ A Γ⇓)) ‘‘×’’ (lower (Term⇓ B Γ⇓)))


   module inner (‘X’ : Type ε) (‘f’ : Term {ε} (‘□’ ‘X’ ‘→’ ‘X’)) where
     ‘H’ : Type ε
     ‘H’ = Quine (W1 ‘Term’ ‘’ ‘VAR₀’ ‘→’ W ‘X’)

     ‘toH’ : □ ((‘□’ ‘H’ ‘→’ ‘X’) ‘→’ ‘H’)
     ‘toH’ = ←SW1SV→W quine←

     ‘fromH’ : □ (‘H’ ‘→’ (‘□’ ‘H’ ‘→’ ‘X’))
     ‘fromH’ = →SW1SV→W quine→

     ‘□‘H’→□‘X’’ : □ (‘□’ ‘H’ ‘→’ ‘□’ ‘X’)
     ‘□‘H’→□‘X’’ = ‘λ∙’ (w ⌜ ‘fromH’ ⌝t w‘‘’’ₐ ‘VAR₀’ w‘‘’’ₐ ‘⌜‘VAR₀’⌝t’)

     ‘h’ : Term ‘H’
     ‘h’ = ‘toH’ ‘’ₐ (‘f’ ‘∘’ ‘□‘H’→□‘X’’)

     Lӧb : □ ‘X’
     Lӧb = ‘fromH’ ‘’ₐ ‘h’ ‘’ₐ ⌜ ‘h’ ⌝t

   Lӧb : ∀ {X} → Term {ε} (‘□’ X ‘→’ X) → Term {ε} X
   Lӧb {X} f = inner.Lӧb X f

   ⌞_⌟ : Type ε → Set _
   ⌞ T ⌟ = Type⇓ T tt

   ‘¬’_ : ∀ {Γ} → Type Γ → Type Γ
   ‘¬’ T = T ‘→’ ‘⊥’

   _w‘‘×’’_ : ∀ {Γ X} → Term {Γ ▻ X} (W (‘Type’ Γ)) → Term {Γ ▻ X} (W (‘Type’ Γ)) → Term {Γ ▻ X} (W (‘Type’ Γ))
   A w‘‘×’’ B = w→ (w→ (w ‘‘×'’’) ‘’ₐ A) ‘’ₐ B

   lӧb : ∀ {‘X’} → □ (‘□’ ‘X’ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
   lӧb f = Term⇓ (Lӧb f) tt

   ¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
   ¬_ {ℓ} T = T → ⊥ {ℓ}

   incompleteness : ¬ □ (‘¬’ (‘□’ ‘⊥’))
   incompleteness = lӧb

   soundness : ¬ □ ‘⊥’
   soundness x = Term⇓ x tt

   non-emptyness : Σ (Type ε) (λ T → □ T)
   non-emptyness = ‘⊤’ , ‘tt’

 open lob

 ‘Bot’ : ∀ {Γ} → Type Γ
 ‘Bot’ {Γ} = Quine (W1 ‘Term’ ‘’ ‘VAR₀’ ‘→’ W1 ‘Term’ ‘’ ‘VAR₀’ ‘→’ W (‘Type’ Γ)) {- a bot takes in the source code for itself, for another bot, and spits out the assertion that it cooperates with this bot -}

 _cooperates-with_ : □ ‘Bot’ → □ ‘Bot’ → Type ε
 b1 cooperates-with b2 = lower (Term⇓ b1 tt (lift b1) (lift b2))

 ‘eval-bot'’ : ∀ {Γ} → Term {Γ} (‘Bot’ ‘→’ (‘□’ ‘Bot’ ‘→’ ‘□’ ‘Bot’ ‘→’ ‘Type’ Γ))
 ‘eval-bot'’ = →SW1SV→SW1SV→W quine→

 ‘‘eval-bot'’’ : ∀ {Γ} → Term {Γ} (‘□’ ‘Bot’ ‘→’ ‘□’ ({- other -} ‘□’ ‘Bot’ ‘→’ ‘Type’ Γ))
 ‘‘eval-bot'’’ = ‘λ∙’ (w ⌜ ‘eval-bot'’ ⌝t w‘‘’’ₐ ‘VAR₀’ w‘‘’’ₐ ‘⌜‘VAR₀’⌝t’)

 ‘other-cooperates-with’ : ∀ {Γ} → Term {Γ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)} (W (W (‘□’ ‘Bot’)) ‘→’ W (W (‘□’ (‘Type’ Γ))))
 ‘other-cooperates-with’ {Γ} = ‘eval-other'’ ‘∘’ w→ (w (w→ (w (‘λ∙’ ‘⌜‘VAR₀’⌝t’))))
   where
     ‘eval-other’ : Term {Γ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)} (W (W (‘□’ (‘□’ ‘Bot’ ‘→’ ‘Type’ Γ))))
     ‘eval-other’ = w→ (w (w→ (w ‘‘eval-bot'’’))) ‘’ₐ ‘VAR₀’

     ‘eval-other'’ : Term (W (W (‘□’ (‘□’ ‘Bot’))) ‘→’ W (W (‘□’ (‘Type’ Γ))))
     ‘eval-other'’ = ww→ (w→ (w (w→ (w ‘‘’ₐ’))) ‘’ₐ ‘eval-other’)

 ‘self’ : ∀ {Γ} → Term {Γ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)} (W (W (‘□’ ‘Bot’)))
 ‘self’ = w ‘VAR₀’

 ‘other’ : ∀ {Γ} → Term {Γ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)} (W (W (‘□’ ‘Bot’)))
 ‘other’ = ‘VAR₀’

 make-bot : ∀ {Γ} → Term {Γ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)} (W (W (‘Type’ Γ))) → Term {Γ} ‘Bot’
 make-bot t = ←SW1SV→SW1SV→W quine← ‘’ₐ ‘λ∙’ (→w (‘λ∙’ t))

 ww‘‘‘¬’’’_ : ∀ {Γ A B}
   → Term {Γ ▻ A ▻ B} (W (W (‘□’ (‘Type’ Γ))))
   → Term {Γ ▻ A ▻ B} (W (W (‘□’ (‘Type’ Γ))))
 ww‘‘‘¬’’’ T = T ww‘‘‘→’’’ w (w ⌜ ⌜ ‘⊥’ ⌝ ⌝t)

 ‘DefectBot’ : □ ‘Bot’
 ‘CooperateBot’ : □ ‘Bot’
 ‘FairBot’ : □ ‘Bot’
 ‘PrudentBot’ : □ ‘Bot’

 ‘DefectBot’ = make-bot (w (w ⌜ ‘⊥’ ⌝))
 ‘CooperateBot’ = make-bot (w (w ⌜ ‘⊤’ ⌝))
 ‘FairBot’ = make-bot (‘‘□’’ (‘other-cooperates-with’ ‘’ₐ ‘self’))
 ‘PrudentBot’ = make-bot (‘‘□’’ (φ₀ ww‘‘‘×’’’ (¬□⊥ ww‘‘‘→’’’ other-defects-against-DefectBot)))
   where
     φ₀ : ∀ {Γ} → Term {Γ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)} (W (W (‘□’ (‘Type’ Γ))))
     φ₀ = ‘other-cooperates-with’ ‘’ₐ ‘self’

     other-defects-against-DefectBot : Term {_ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)} (W (W (‘□’ (‘Type’ _))))
     other-defects-against-DefectBot = ww‘‘‘¬’’’ (‘other-cooperates-with’ ‘’ₐ w (w ⌜ ‘DefectBot’ ⌝t))

     ¬□⊥ : ∀ {Γ A B} → Term {Γ ▻ A ▻ B} (W (W (‘□’ (‘Type’ Γ))))
     ¬□⊥ = w (w ⌜ ⌜ ‘¬’ (‘□’ ‘⊥’) ⌝ ⌝t)

\end{code}

\section{Encoding with Add-Quote Function}
(appendix)
  - Discuss whiteboard phrasing of sentence with sigmas
    - It remains to show that we can construct
  - Discuss whiteboard phrasing of untyped sentence
    - Given:
      - X
      - □ = Term
      - f : □ 'X' -> X
      - define y : X
      - Suppose we have a type H ≅ Term ⌜ H → X ⌝, and we have
        - toH : Term ⌜ H → X ⌝ → H
        - fromH : H → Term ⌜ H → X ⌝
        - quote : H → Term ⌜ H ⌝
        -
      - Then we can define
      - \verb|y = (λ h : H. f (subst (quote h) h) (toH '\h : H. f (subst (quote h) h)')...|
\section{Removing add-quote and actually tying the knot (future work 1)}

- Bibliography
- Appendix
- Temporary outline section to be moved
  -
  - How do we construct the Curry--Howard analogue of the L\"obian sentence?  A quine is a program that outputs its own source code~\cite{}.  We will say that a \emph{type-theoretic quine} is a program that outputs its own (well-typed) abstract syntax tree.  Generalizing this slightly, we can consider programs that output an arbitrary function of their own syntax trees.
  - TODO: Examples of double quotation, single quotation, etc.
  - Given any function φ from doubly-quoted syntactic types to singly-quoted syntactic types, and given an operator \verb|⌜_⌝| which adds an extra level of quotation, we can define the type of a \emph{quine at φ} to be a (syntactic) type "Quine φ" which is isomorphic to "φ (⌜Quine φ ⌝))".
  - What's wrong is that self-reference with truth is impossible.  In a particular technical sense, it doesn't terminate.  Solution: Provability
  - Quining / self-referential provability sentence and provability implies truth
  - Curry--Howard, quines, abstract syntax trees (This is an interpreter!)

\appendix
\input{lob-appendix.tex}

This is the text of the appendix, if you need one.

\acks

Acknowledgments, if needed.

% We recommend abbrvnat bibliography style.

\bibliographystyle{abbrvnat}

% The bibliography should be embedded for final submission.

\begin{thebibliography}{}
\softraggedright

\bibitem[Smith et~al.(2009)Smith, Jones]{smith02}
P. Q. Smith, and X. Y. Jones. ...reference text...

\end{thebibliography}


 \end{document}
