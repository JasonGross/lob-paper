 \documentclass[preprint]{sigplanconf}

 \usepackage{agda}

 % The following packages are needed because unicode
 % is translated (using the next set of packages) to
 % latex commands. You may need more packages if you
 % use more unicode characters:

 \usepackage{amssymb}
 \usepackage{hyperref}
 \usepackage{xcolor}
 % \usepackage{bbm}
 % \usepackage[greek,english]{babel}

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
 What is the computational equivalent of the sentence "If this sentence is provable, then X"?  It will be something of the form "??? -> X".  As a warm-up, let's look at a Python program that returns a string representation of this type.

 To do this, we need a program that outputs its own source code.  There are three genuinely distinct solutions, the first of which is degenerate, and the second of which is cheeky (or sassy?).  These "cheating" solutions are:
 \begin{itemize}
   \item The empty program, which outputs nothing.
   \item The program \verb|print(open(__file__, 'r').read())|, which relies on the Python interpreter to get the source code of the program.
 \end{itemize}

 Now we develop the standard solution.  At a first gloss, it looks like:
\begin{verbatim}
 (lambda my_type: '(' + my_type + ') -> X') "???"
\end{verbatim}

 Now we need to replace "???" with the entirety of this program code.  We use Python's string escaping function (repr) and replacement syntax ("foo %s bar" % "baz" becomes "foo baz bar"):

\begin{verbatim}
 (lambda my_type: '(' + my_type % repr(my_type) + ') -> X')
   ("(lambda my_type: '(' + my_type %% repr(my_type) + ') -> X')\n  (%s)")
\end{verbatim}
 This is a slight modification on the standard way of programming a quine, a program that outputs its own source-code.
 Suppose we have a function □ that takes in a string representation of a type, and returns the type of syntax trees of programs producing that type.  Then our L\"obian sentence would look something like (if "->" were valid notation for function types in Python)
\begin{verbatim}
 (lambda my_type: □ (my_type % repr(my_type)) -> X)
   ("(lambda my_type: □ (my_type %% repr(my_type)) -> X)\n  (%s)")
\end{verbatim}
 Now, finally, we can see what goes wrong when we consider using "if this sentence is true" rather than "if this sentence is provable".  Provability corresponds to syntax trees for programs; truth corresponds to execution of the program itself.  Our pseudo-Python thus becomes
\begin{verbatim}
 (lambda my_type: eval(my_type % repr(my_type)) -> X)
   ("(lambda my_type: eval(my_type %% repr(my_type)) -> X)\n  (%s)")
\end{verbatim}

 This code never terminates!  So, in a quite literal sense, the issue with our original sentence was that, if we tried to phrase it, we'd never finish.

 Note well that the type (□ X -> X) is a type that takes syntax trees and evaluates them; it is the type of an interpreter.  (TODO: maybe move this sentence?)

\section{Abstract Syntax Trees for Dependent Type Theory}

  The idea of formalizing a type of syntax trees which only permits well-typed programs is common in the literature.  (TODO: citations)  For example, here is a very simple (and incomplete) formalization with $\Pi$, a unit type (⊤), an empty type (⊥), and lambdas.  (FIXME: What's the right level of simplicity?)

  We begin with some standard data type declarations.

\begin{code}
open import Agda.Primitive public
  using    (Level; _⊔_; lzero; lsuc)

infixl 1 _,_

record ⊤ {ℓ} : Set ℓ where
  constructor tt

data ⊥ {ℓ} : Set ℓ where

record Σ {ℓ ℓ′} (A : Set ℓ) (P : A → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : P proj₁

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

  - In this paper, we make extensive use of this trick for validating models.  We formalize the simplest syntax that supports L\"ob's theorem and prove it sound relative to Agda in 10 lines of code; the understanding is that this syntax could be extended to support basically anything you might want.  We then present an extended version of this solution, which supports enough operations that we can prove our syntax sound (consistent), incomplete, and nonempty.  In a hundred lines of code, we prove L\"ob's theorem under the assumption that we are given a quine; this is basically the well-typed functional version of the program that uses \verb|open(__file__, 'r').read()|.  Finally, we sketch our implementation of L\"ob's theorem (code in an appendix) based on the assumption only that we can add a level of quotation to our syntax tree; this is the equivalent of letting the compiler implement repr(), rather than implementing it ourselves.  We close with an application to the prisoner's dilemma, as well as some discussion about avenues for removing the hard-coded repr.
- Prior Work
  - Use of L\"ob's theorem in program logic as an induction principle? (TODO)
  - Brief mention of Lob's theorem in Haskell / elsewhere / ? (TODO)
- Trivial encoding
- Encoding with completeness soundness and incompleteness
- Encoding with quines
- Trivial encoding
  -
- Digression: Application of quining to prisoner's dilemma???
- Encoding with add-quote function (appendix)
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
- Removing add-quote and actually tying the knot (future work 1)
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
\section{Appendix Title}

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
