\input{./header.tex}

\title{Lӧb's Theorem}
\subtitle{A functional pearl of dependently typed quining}

\maketitle

%\category{CR-number}{subcategory}{third-level}

% general terms are not compulsory anymore,
% you may leave them out
%\terms
%Agda, Lob, quine, self-reference

\keywords
Agda, Lӧb's theorem, quine, self-reference, type theory

\AgdaHide{
  \begin{code}
module lob where
  \end{code}
}

\begin{abstract}
Lӧb's theorem states that to prove that a proposition is provable, it
is sufficient to prove the proposition under the assumption that it is
provable.  The Curry-Howard isomorphism identifies formal proofs with
abstract syntax trees of programs; Lӧb's theorem thus implies that
quoted self-interpreters are impossible for total languages.  We
formalize a few variations of Lӧb's theorem in Agda using an
inductive-inductive encoding of terms indexed over types.  We verify
the consistency of our formalizations relative to Agda by giving them
semantics via interpretation functions.
\end{abstract}

\begin{quotation}
\noindent \textit{If P's answer is `Bad!', Q will suddenly stop. \\
But otherwise, Q will go back to the top, \\
and start off again, looping endlessly back, \\
till the universe dies and turns frozen and black.}
\end{quotation}
\begin{flushright}
Excerpt from \emph{Scooping the Loop Snooper: A proof that the Halting Problem is undecidable} \cite{loopsnoop}
\end{flushright}

% \todo{Should we unify the various repr-like functions (repr, add-quote, ⌜_⌝ᵀ, ⌜_⌝ᵗ, ⌜_⌝ᶜ)?}

\section{Introduction}

 Lӧb's theorem has a variety of applications, from providing an
 induction rule for program semantics involving a ``later''
 operator~\cite{appel2007very}, to proving incompleteness of a logical
 theory as a trivial corollary, from acting as a no-go theorem for a
 large class of self-interpreters, to allowing robust cooperation in
 the Prisoner's Dilemma with Source
 Code~\cite{BaraszChristianoFallensteinEtAl2014}, and even in one case
 curing social anxiety~\cite{Yudkowsky2014}.

 In this paper, after introducing the content of Lӧb's theorem, we
 will present three formalizations in Agda: one that shows the theorem
 is admissible as an axiom in a wide range of situations, one which
 proves Lӧb's theorem by assuming quines, and one which constructs
 the proof under even weaker assumptions; see
 \autoref{sec:prior-work-and-new} for details.

 ``What is Lӧb's theorem, this versatile tool with wondrous
 applications?'' you may ask.

 Consider the sentence ``if this sentence is true, then you, dear
 reader, are the most awesome person in the world.''  Suppose that
 this sentence is true.  Then you, dear reader are the most awesome
 person in the world.  Since this is exactly what the sentence
 asserts, the sentence is true, and you, dear reader, are the most
 awesome person in the world.  For those more comfortable with
 symbolic logic, we can let $X$ be the statement ``you, dear reader,
 are the most awesome person in the world'', and we can let $A$ be the
 statement ``if this sentence is true, then $X$''.  Since we have that
 $A$ and $A → X$ are the same, if we assume $A$, we are also assuming
 $A → X$, and hence we have $X$.  Thus since assuming $A$ yields $X$,
 we have that $A → X$.  What went wrong?\footnote{Those unfamiliar
 with conditionals should note that the ``if \ldots\space then
 \ldots'' we use here is the logical ``if'', where ``if false then
 $X$'' is always true, and not the counter-factual ``if''.}

 It can be made quite clear that something is wrong; the more common
 form of this sentence is used to prove the existence of Santa Claus
 to logical children: considering the sentence ``if this sentence is
 true, then Santa Claus exists'', we can prove that Santa Claus
 exists.  By the same logic, though, we can prove that Santa Claus
 does not exist by considering the sentence ``if this sentence is
 true, then Santa Claus does not exist.''  Whether you consider it
 absurd that Santa Claus exist, or absurd that Santa Claus not exist,
 surely you will consider it absurd that Santa Claus both exist and
 not exist.  This is known as Curry's Paradox.

 Have you figured out what went wrong?

 The sentence that we have been considering is not a valid
 mathematical sentence.  Ask yourself what makes it invalid, while we
 consider a similar sentence that is actually valid.

 Now consider the sentence``if this sentence is provable, then you,
 dear reader, are the most awesome person in the world.''  Fix a
 particular formalization of provability (for example, Peano
 Arithmetic, or Martin--Lӧf Type Theory).  To prove that this
 sentence is true, suppose that it is provable.  We must now show that
 you, dear reader, are the most awesome person in the world.  \emph{If
 provability implies truth}, then the sentence is true, and thus you,
 dear reader, are the most awesome person in the world.  Hence, if we
 can assume that provability implies truth, then we can prove that the
 sentence is true.  This, in a nutshell, is Lӧb's theorem: to prove
 $X$, it suffices to prove that $X$ is true whenever $X$ is provable.
 Symbolically, this is $$□ (□ X → X) → □ X$$ where $□ X$ means ``$X$
 is provable'' (in our fixed formalization of provability).

 Let us now return to the question we posed above: what went wrong
 with our original sentence?  The answer is that self-reference with
 truth is impossible, and the clearest way we know to argue for this is
 via the Curry--Howard Isomorphism; in a particular technical sense,
 the problem is that self-reference with truth fails to terminate.

 The Curry--Howard Isomorphism establishes an equivalence between
 types and propositions, between (well-typed, terminating, functional)
 programs and proofs.  See \autoref{table:curry-howard} for some
 examples.  Now we ask: what corresponds to a formalization of
 provability?  If a proof of P is a terminating functional program
 which is well-typed at the type corresponding to P, and to assert
 that P is provable is to assert that the type corresponding to P is
 inhabited, then an encoding of a proof is an encoding of a program.
 Although mathematicians typically use Gӧdel codes to encode
 propositions and proofs, a more natural choice of encoding programs
 will be abstract syntax trees.  In particular, a valid syntactic
 proof of a given (syntactic) proposition corresponds to a well-typed
 syntax tree for an inhabitant of the corresponding syntactic type.

  \begin{table}
  \begin{center}
  \begin{tabular}{ccc}
  Logic & Programming & Set Theory \\ \hline
  Proposition & Type & Set of Proofs \\
  Proof & Program & Element \\
  Implication (→) & Function (→) & Function  \\
  Conjunction (∧) & Pairing (,) & Cartesian Product (×)  \\
  Disjunction (∨) & Sum (+) & Disjoint Union (⊔) \\
  Gӧdel codes & ASTs & ---
  \end{tabular}
  \end{center}
  \caption{The Curry-Howard isomorphism between mathematical logic and functional programming} \label{table:curry-howard}
  \end{table}

 Unless otherwise specified, we will henceforth consider only
 well-typed, terminating programs; when we say ``program'', the
 adjectives ``well-typed'' and ``terminating'' are implied.

% Before diving into Lӧb's theorem in detail, we'll first visit a
% standard paradigm for formalizing the syntax of dependent type
% theory. (\todo{Move this?})

\section{Quines}

 What is the computational equivalent of the sentence ``If this
 sentence is provable, then $X$''?  It will be something of the form
 ``??? → $X$''.  As a warm-up, let's look at a Python program that
 returns a string representation of this type.

 To do this, we need a program that outputs its own source code.
 There are three genuinely distinct solutions, the first of which is
 degenerate, and the second of which is cheeky (or sassy?).  These
 ``cheating'' solutions are:
 \begin{itemize}
   \item The empty program, which outputs nothing.
   \item The code
     \mintinline{python}|print(open(__file__, 'r').read())|,
     which relies on the Python interpreter to get the
     source code of the program.
 \end{itemize}

 Now we develop the standard solution.  At a first gloss, it looks
 like:
\begin{minted}[mathescape,
%               numbersep=5pt,
               gobble=2,
%               frame=lines,
%               framesep=2mm%
]{python}
  (lambda T: '(' + T + ') → X') "???"
\end{minted}

 Now we need to replace \mintinline{python}|"???"| with the entirety
 of this program code.  We use Python's string escaping function
 (\mintinline{python}|repr|) and replacement syntax
 (\mintinline{python}|("foo %s bar" % "baz")| becomes
 \mintinline{python}|"foo baz bar"|):

\begin{minted}[gobble=2]{python}
  (lambda T: '(' + T % repr(T) + ') → X')
   ("(lambda T: '(' + T %% repr(T) + ') → X')\n (%s)")
\end{minted}
 This is a slight modification on the standard way of programming a
 quine, a program that outputs its own source-code.

 Suppose we have a function □ that takes in a string representation of
 a type, and returns the type of syntax trees of programs producing
 that type.  Then our Lӧbian sentence would look something like (if
 → were valid notation for function types in Python)
\begin{minted}[gobble=1]{python}
 (lambda T: □ (T % repr(T)) → X)
  ("(lambda T: □ (T %% repr(T)) → X)\n (%s)")
\end{minted}
 Now, finally, we can see what goes wrong when we consider using ``if
 this sentence is true'' rather than ``if this sentence is provable''.
 Provability corresponds to syntax trees for programs; truth
 corresponds to execution of the program itself.  Our pseudo-Python
 thus becomes \label{sec:python-quine}
\begin{minted}[gobble=1]{python}
 (lambda T: eval(T % repr(T)) → X)
  ("(lambda T: eval(T %% repr(T)) → X)\n (%s)")
\end{minted}

 This code never terminates!  So, in a quite literal sense, the issue
 with our original sentence was that, if we tried to phrase it, we'd
 never finish.

 Note well that the type (□ X → X) is a type that takes syntax trees
 and evaluates them; it is the type of an interpreter.
% (\todo{maybe move this sentence?})

\section{Abstract Syntax Trees for Dependent Type Theory}

  The idea of formalizing a type of syntax trees which only permits
  well-typed programs is common in the
  literature~\cite{mcbride2010outrageous,Chapman200921,danielsson2006formalisation}.
  For example, here is a very simple (and incomplete) formalization
  with dependent function types ($\Pi$), a unit type (⊤), an empty
  type (⊥), and functions ($\lambda$).

  We will use some standard data type declarations, which are provided
  for completeness in \autoref{sec:common}.
 \AgdaHide{
  \begin{code}
open import common public
  \end{code}
}
\AgdaHide{
  \begin{code}
module dependent-type-theory where
  \end{code}
}

\noindent
\begin{code}
 mutual
  infixl 2 _▻_

  data Context : Set where
   ε : Context
   _▻_ : (Γ : Context) → Type Γ → Context

  data Type : Context → Set where
   ‘⊤’ : ∀ {Γ} → Type Γ
   ‘⊥’ : ∀ {Γ} → Type Γ
   ‘Π’ : ∀ {Γ}
     → (A : Type Γ) → Type (Γ ▻ A) → Type Γ

  data Term : {Γ : Context} → Type Γ → Set where
   ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
   ‘λ’ : ∀ {Γ A B} → Term B → Term {Γ} (‘Π’ A B)
 \end{code}

  An easy way to check consistency of a syntactic theory which is
  weaker than the theory of the ambient proof assistant is to define
  an interpretation function, also commonly known as an unquoter, or a
  denotation function, from the syntax into the universe of types.
  Here is an example of such a function:

\begin{code}
 mutual
  ⟦_⟧ᶜ : Context → Set
  ⟦ ε ⟧ᶜ     = ⊤
  ⟦ Γ ▻ T ⟧ᶜ = Σ ⟦ Γ ⟧ᶜ ⟦ T ⟧ᵀ

  ⟦_⟧ᵀ : ∀ {Γ}
    → Type Γ → ⟦ Γ ⟧ᶜ → Set
  ⟦ ‘⊤’ ⟧ᵀ Γ⇓     = ⊤
  ⟦ ‘⊥’ ⟧ᵀ Γ⇓     = ⊥
  ⟦ ‘Π’ A B ⟧ᵀ Γ⇓ = (x : ⟦ A ⟧ᵀ Γ⇓) → ⟦ B ⟧ᵀ (Γ⇓ , x)

  ⟦_⟧ᵗ : ∀ {Γ T}
    → Term {Γ} T → (Γ⇓ : ⟦ Γ ⟧ᶜ) → ⟦ T ⟧ᵀ Γ⇓
  ⟦ ‘tt’ ⟧ᵗ Γ⇓    = tt
  ⟦ ‘λ’ f ⟧ᵗ Γ⇓ x = ⟦ f ⟧ᵗ (Γ⇓ , x)
\end{code}

  Note that this interpretation function has an essential property
  that we will call \emph{locality}: the interpretation of any given
  constructor does not require doing case analysis on any of its
  arguments.  By contrast, one could imagine an interpretation
  function that interpreted function types differently depending on
  their domain and codomain; for example, one might interpret
  \mintinline{Agda}|‘⊥’ ‘→’ A| as
  \mintinline{Agda}|⊤|. \label{sec:local-interpretation}

\section{This Paper}

 In this paper, we make extensive use of this trick for validating
 models.  In \autoref{sec:12-lines}, we formalize the simplest syntax
 that supports Lӧb's theorem and prove it sound relative to Agda in 12
 lines of code; the understanding is that this syntax could be
 extended to support basically anything you might want.  We then
 present in \autoref{sec:extended-trivial} an extended version of this
 solution, which supports enough operations that we can prove our
 syntax sound (consistent), incomplete, and nonempty.  In a hundred
 lines of code, we prove Lӧb's theorem in
 \autoref{sec:100-lines-quine} under the assumption that we are given
 a quine; this is basically the well-typed functional version of the
 program that uses \mintinline{python}|open(__file__, 'r').read()|.
 After taking a digression for an application of Lӧb's theorem to the
 prisoner's dilemma in \autoref{sec:prisoner}, we sketch in
 \autoref{sec:only-add-quote} our implementation of Lӧb's theorem
 (code in the supplemental material) based on only the assumption that
 we can add a level of quotation to our syntax tree; this is the
 equivalent of letting the compiler implement
 \mintinline{python}|repr|, rather than implementing it ourselves.  We
 close in \autoref{sec:future-work} with some discussion about avenues
 for removing the hard-coded \mintinline{python}|repr|.

\section{Prior Work} \label{sec:prior-work-and-new}

 There exist a number of implementations or formalizations of various
 flavors of Lӧb's theorem in the literature.
 \Citeauthor{appel2007very} use Lӧb's theorem as an induction rule for
 program logics in Coq~\cite{appel2007very}.
 \Citeauthor{piponi-from-l-theorem-to-spreadsheet} formalizes a rule
 with the same shape as Lӧb's theorem in Haskell, and uses it for,
 among other things, spreadsheet
 evaluation~\cite{piponi-from-l-theorem-to-spreadsheet}.

 Gӧdel's incompleteness theorems, easy corrolaries to Lӧb's theorem,
 have been formally verified numerous
 times~\cite{Shankar:1986:PM:913294,shankar1997metamathematics,DBLP:journals/corr/abs-cs-0505034}.

 To our knowledge, our twelve line proof is the shortest
 self-contained formally verified proof of the admissibility of Lӧb's
 theorem to date.  We are not aware of other formally verified proofs
 of Lӧb's theorem which interpret the modal □ operator as an
 inductively defined type of syntax trees of proofs of a given
 theorem, as we do in this formalization.  Finally, we are not aware
 of other work which uses the trick of talking about a local
 interpretation function (as described at the end of
 \autoref{sec:local-interpretation}) to talk about consistent
 extensions to classes of encodings of type theory.

\section{Trivial Encoding} \label{sec:12-lines}
\AgdaHide{
  \begin{code}
module trivial-encoding where
 infixr 1 _‘→’_
  \end{code}
}

 We begin with a language that supports almost nothing other than
 Lӧb's theorem.  We use \mintinline{Agda}|□ T| to denote the type of
 \mintinline{Agda}|Term|s of whose syntactic type is
 \mintinline{Agda}|T|.  We use \mintinline{Agda}|‘□’ T| to denote the
 syntactic type corresponding to the type of (syntactic) terms whose
 syntactic type is \mintinline{Agda}|T|.  For example, the type of a
 \mintinline{python}|repr| which operated on syntax trees would be
 \mintinline{Agda}|□ T → □ (‘□’ T)|.

\begin{code}
 data Type : Set where
   _‘→’_ : Type → Type → Type
   ‘□’ : Type → Type

 data □ : Type → Set where
   Lӧb : ∀ {X} → □ (‘□’ X ‘→’ X) → □ X
\end{code}
 The only term supported by our term language is Lӧb's theorem.  We
 can prove this language consistent relative to Agda with an
 interpreter:

\begin{code}
 ⟦_⟧ᵀ : Type → Set
 ⟦ A ‘→’ B ⟧ᵀ = ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ
 ⟦ ‘□’ T ⟧ᵀ   = □ T

 ⟦_⟧ᵗ : ∀ {T : Type} → □ T → ⟦ T ⟧ᵀ
 ⟦ Lӧb □‘X’→X ⟧ᵗ = ⟦ □‘X’→X ⟧ᵗ (Lӧb □‘X’→X)
\end{code}
 To interpret Lӧb's theorem applied to the syntax for a compiler $f$
 (\mintinline{Agda}|□‘X’→X| in the code above), we interpret $f$, and
 then apply this interpretation to the constructor
 \mintinline{Agda}|Lӧb| applied to $f$.

 Finally, we tie it all together:

\begin{code}
 lӧb : ∀ {‘X’} → □ (‘□’ ‘X’ ‘→’ ‘X’) → ⟦ ‘X’ ⟧ᵀ
 lӧb f = ⟦ Lӧb f ⟧ᵗ
\end{code}

 This code is deceptively short, with all of the interesting work
 happening in the interpretation of \mintinline{Agda}|Lӧb|.

 What have we actually proven, here?  It may seem as though we've
 proven absolutely nothing, or it may seem as though we've proven that
 Lӧb's theorem always holds.  Neither of these is the case.  The
 latter is ruled out, for example, by the existence of an
 self-interpreter for
 F$_\omega$~\cite{brown2016breaking}.\footnote{One may wonder how
 exactly the self-interpreter for F$_\omega$ does not contradict this
 theorem.  In private conversations with Matt Brown, we found that the
 F$_\omega$ self-interpreter does not have a separate syntax for
 types, instead indexing its terms over types in the metalanguage.
 This means that the type of Lӧb's theorem becomes either
 \mintinline{Agda}|□ (□ X → X) → □ X|, which is not strictly positive,
 or \mintinline{Agda}|□ (X → X) → □ X|, which, on interpretation, must
 be filled with a general fixpoint operator.  Such an operator is
 well-known to be inconsistent.}

 We have proven the following.  Suppose you have a formalization of
 type theory which has a syntax for types, and a syntax for terms
 indexed over those types.  If there is a ``local explanation'' for
 the system being sound, i.e., an interpretation function where each
 rule does not need to know about the full list of constructors, then
 it is consistent to add a constructor for Lӧb's theorem to your
 syntax.  This means that it is impossible to contradict Lӧb's theorem
 no matter what (consistent) constructors you add.  We will see in the
 next section how this gives incompleteness, and discuss in later
 sections how to \emph{prove Lӧb's theorem}, rather than simply
 proving that it is consistent to assume.

\section{Encoding with Soundness, Incompleteness, and Non-Emptiness} \label{sec:extended-trivial}

 By augmenting our representation with top (\mintinline{Agda}|‘⊤’|)
 and bottom (\mintinline{Agda}|‘⊥’|) types, and a unique inhabitant of
 \mintinline{Agda}|‘⊤’|, we can prove soundness, incompleteness, and
 non-emptiness.

\AgdaHide{
  \begin{code}
module sound-incomplete-nonempty where
 infixr 1 _‘→’_
  \end{code}
}

\begin{code}
 data Type : Set where
  _‘→’_ : Type → Type → Type
  ‘□’ : Type → Type
  ‘⊤’ : Type
  ‘⊥’ : Type

 ---- "□" is sometimes written as "Term"
 data □ : Type → Set where
  Lӧb : ∀ {X} → □ (‘□’ X ‘→’ X) → □ X
  ‘tt’ : □ ‘⊤’

 ⟦_⟧ᵀ : Type → Set
 ⟦ A ‘→’ B ⟧ᵀ = ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ
 ⟦ ‘□’ T ⟧ᵀ   = □ T
 ⟦ ‘⊤’ ⟧ᵀ     = ⊤
 ⟦ ‘⊥’ ⟧ᵀ     = ⊥

 ⟦_⟧ᵗ : ∀ {T : Type} → □ T → ⟦ T ⟧ᵀ
 ⟦ Lӧb □‘X’→X ⟧ᵗ = ⟦ □‘X’→X ⟧ᵗ (Lӧb □‘X’→X)
 ⟦ ‘tt’ ⟧ᵗ = tt

 ‘¬’_ : Type → Type
 ‘¬’ T = T ‘→’ ‘⊥’

 lӧb : ∀ {‘X’} → □ (‘□’ ‘X’ ‘→’ ‘X’) → ⟦ ‘X’ ⟧ᵀ
 lӧb f = ⟦ Lӧb f ⟧ᵗ

 ---- There is no syntactic proof of absurdity
 soundness : ¬ □ ‘⊥’
 soundness x = ⟦ x ⟧ᵗ

 ---- but it would be absurd to have a syntactic
 ---- proof of that fact
 incompleteness : ¬ □ (‘¬’ (‘□’ ‘⊥’))
 incompleteness = lӧb

 ---- However, there are syntactic proofs of some
 ---- things (namely ⊤)
 non-emptiness : □ ‘⊤’
 non-emptiness = ‘tt’

 ---- There are no syntactic interpreters, things
 ---- which, at any type, evaluate code at that
 ---- type to produce its result.
 no-interpreters : ¬ (∀ {‘X’} → □ (‘□’ ‘X’ ‘→’ ‘X’))
 no-interpreters interp = lӧb (interp {‘⊥’})
\end{code}

  What is this incompleteness theorem?  Gӧdel's incompleteness theorem
  is typically interpred as ``there exist true but unprovable
  statements.''  In intuitionistic logic, this is hardly surprising.
  A more accurate rendition of the theorem in Agda might be ``there
  exist true but inadmissible statements,'' i.e., there are statements
  which are provable meta-theoretically, but which lead to
  (meta-theoretically--provable) inconsistency if assumed at the
  object level.

  This may seem a bit esoteric, so let's back up a bit, and make it
  more concrete.  Let's begin by banishing ``truth''.  Sometimes it is
  useful to formalize a notion of provability.  For example, you might
  want to show neither assuming $T$ nor assuming $¬T$ yields a proof
  of contradiction.  You cannot phrase this is $¬T ∧ ¬¬T$, for that is
  absurd.  Instead, you want to say something like $(¬□T) ∧ ¬□(¬T)$,
  i.e., it would be absurd to have a proof object of either $T$ or of
  $¬T$.  After a while, you might find that meta-programming in this
  formal syntax is nice, and you might want it to be able to formalize
  every proof, so that you can do all of your solving reflectively.
  If you're like us, you might even want to reason about the
  reflective tactics themselves in a reflective manner; you'd want to
  be able to add levels of quotation to quoted things to talk about
  such tactics.

  The incompleteness theorem, then, is this: your reflective system,
  no matter how powerful, cannot formalize every proof.  For any fixed
  language of syntactic proofs which is powerful enough to represent
  itself, there will always be some valid proofs that you cannot
  reflect into your syntax.  In particular, you might be able to prove
  that your syntax has no proofs of ⊥ (by interpreting any such
  proof).  But you'll be unable to quote that proof.  This is what the
  incompleteness theorem stated above says.  Incompleteness,
  fundamentally, is a result about the limitations of formalizing
  provability.

\section{Encoding with Quines} \label{sec:100-lines-quine}

 \AgdaHide{
  \begin{code}
module lob-by-quines where
  \end{code}
}

 We now weaken our assumptions further.  Rather than assuming Lӧb's
 theorem, we instead assume only a type-level quine in our
 representation.  Recall that a \emph{quine} is a program that outputs
 some function of its own source code.  A \emph{type-level quine at ϕ}
 is program that outputs the result of evaluating the function ϕ on
 the abstract syntax tree of its own type.  Letting
 \mintinline{Agda}|Quine ϕ| denote the constructor for a type-level
 quine at ϕ, we have an isomorphism between \mintinline{Agda}|Quine ϕ|
 and \mintinline{Agda}|ϕ ⌜ Quine ϕ ⌝ᵀ|, where
 \mintinline{Agda}|⌜ Quine ϕ ⌝ᵀ| is the abstract syntax tree for the
 source code of \mintinline{Agda}|Quine ϕ|.  Note that we assume
 constructors for ``adding a level of quotation'', turning abstract
 syntax trees for programs of type $T$ into abstract syntax trees for
 abstract syntax trees for programs of type $T$; this corresponds to
 \mintinline{Python}|repr|.

\begin{code}
 infixl 3 _‘’ₐ_
 infixl 3 _w‘‘’’ₐ_
 infixl 3 _‘’_
 infixl 2 _▻_
 infixr 2 _‘∘’_
 infixr 1 _‘→’_
\end{code}

 We begin with an encoding of contexts and types, repeating from above
 the constructors of ‘→’, ‘□’, ‘⊤’, and ‘⊥’.  We add to this a
 constructor for quines (\mintinline{Agda}|Quine|), and a constructor
 for syntax trees of types in the empty context (‘Typeε’).  Finally,
 rather than proving weakening and substitution as mutually recursive
 definitions, we take the easier but more verbose route of adding
 constructors that allow adding and substituting extra terms in the
 context. Note that ‘□’ is now a function of the represented language,
 rather than a meta-level operator.

% \todo{Does this need more explanation?}
% \todo{\cite{mcbride2010outrageous}}

 Note that we use the infix operator \mintinline{Agda}|_‘’_| to denote
 substitution.

\begin{code}
 mutual
  data Context : Set where
   ε : Context
   _▻_ : (Γ : Context) → Type Γ → Context

  data Type : Context → Set where
   _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
   ‘⊤’ : ∀ {Γ} → Type Γ
   ‘⊥’ : ∀ {Γ} → Type Γ
   ‘Typeε’ : ∀ {Γ} → Type Γ
   ‘□’ : ∀ {Γ} → Type (Γ ▻ ‘Typeε’)
   Quine : Type (ε ▻ ‘Typeε’) → Type ε
   W : ∀ {Γ A}
     → Type Γ → Type (Γ ▻ A)
   W₁ : ∀ {Γ A B}
     → Type (Γ ▻ B) → Type (Γ ▻ A ▻ (W B))
   _‘’_ : ∀ {Γ A}
     → Type (Γ ▻ A) → Term A → Type Γ
\end{code}

  In addition to ‘λ’ and ‘tt’, we now have the AST-equivalents of
  Python's \mintinline{Python}|repr|, which we denote as
  \mintinline{Agda}|⌜_⌝ᵀ| for the type-level add-quote function, and
  \mintinline{Agda}|⌜_⌝ᵗ| for the term-level add-quote function.  We
  add constructors \mintinline{Agda}|quine→| and
  \mintinline{Agda}|quine←| that exhibit the isomorphism that defines
  our type-level quine constructor, though we elide a constructor
  declaring that these are inverses, as we find it unnecessary.

  To construct the proof of Lӧb's theorem, we need a few other
  standard constructors, such as \mintinline{Agda}|‘VAR₀’|, which
  references a term in the context; \mintinline{Agda}|_‘’ₐ_|, which we
  use to denote function application; \mintinline{Agda}|_‘∘’_|, a
  function composition operator; and \mintinline{Agda}|‘⌜‘VAR₀’⌝ᵗ’|,
  the variant of \mintinline{Agda}|‘VAR₀’| which adds an extra level
  of syntax-trees. We also include a number of constructors that
  handle weakening and substitution; this allows us to avoid both
  inductive-recursive definitions of weakening and substitution, and
  defining a judgmental equality or conversion relation.

\begin{code}
  data Term : {Γ : Context} → Type Γ → Set where
   ‘λ’ : ∀ {Γ A B}
     → Term {Γ ▻ A} (W B) → Term (A ‘→’ B)
   ‘tt’ : ∀ {Γ}
     → Term {Γ} ‘⊤’
   ⌜_⌝ᵀ : ∀ {Γ}
     → Type ε
     → Term {Γ} ‘Typeε’
   ⌜_⌝ᵗ : ∀ {Γ T}
     → Term {ε} T
     → Term {Γ} (‘□’ ‘’ ⌜ T ⌝ᵀ)
   quine→ : ∀ {ϕ}
     → Term {ε} (Quine ϕ           ‘→’ ϕ ‘’ ⌜ Quine ϕ ⌝ᵀ)
   quine← : ∀ {ϕ}
     → Term {ε} (ϕ ‘’ ⌜ Quine ϕ ⌝ᵀ ‘→’ Quine ϕ)
   ---- The constructors below here are for
   ---- variables, weakening, and substitution
   ‘VAR₀’ : ∀ {Γ T}
     → Term {Γ ▻ T} (W T)
   _‘’ₐ_ : ∀ {Γ A B}
    → Term {Γ} (A ‘→’ B)
    → Term {Γ} A
    → Term {Γ} B
   _‘∘’_ : ∀ {Γ A B C}
    → Term {Γ} (B ‘→’ C)
    → Term {Γ} (A ‘→’ B)
    → Term {Γ} (A ‘→’ C)
   ‘⌜‘VAR₀’⌝ᵗ’ : ∀ {T}
     → Term {ε ▻ ‘□’ ‘’ ⌜ T ⌝ᵀ}
            (W (‘□’ ‘’ ⌜ ‘□’ ‘’ ⌜ T ⌝ᵀ ⌝ᵀ))
   →SW₁SV→W : ∀ {Γ T X A B} {x : Term {Γ} X}
     → Term (T ‘→’ (W₁ A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x)
     → Term (T ‘→’ A ‘’ x ‘→’ B)
   ←SW₁SV→W : ∀ {Γ T X A B} {x : Term {Γ} X}
     → Term ((W₁ A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x ‘→’ T)
     → Term ((A ‘’ x ‘→’ B) ‘→’ T)
   w : ∀ {Γ A T} → Term A → Term {Γ ▻ T} (W A)
   w→ : ∀ {Γ A B X}
    → Term {Γ} (A ‘→’ B)
    → Term {Γ ▻ X} (W A ‘→’ W B)
   _w‘‘’’ₐ_ : ∀ {A B T}
    → Term {ε ▻ T} (W (‘□’ ‘’ ⌜ A ‘→’ B ⌝ᵀ))
    → Term {ε ▻ T} (W (‘□’ ‘’ ⌜ A ⌝ᵀ))
    → Term {ε ▻ T} (W (‘□’ ‘’ ⌜ B ⌝ᵀ))

 □ : Type ε → Set _
 □ = Term {ε}
\end{code}

 To verify the soundness of our syntax, we provide a model for it and
 an interpretation into that model.  We call particular attention to
 the interpretation of \mintinline{Agda}|‘□’|, which is just
 \mintinline{Agda}|Term {ε}|; to \mintinline{Agda}|Quine ϕ|, which is
 the interpretation of \mintinline{Agda}|ϕ| applied to
 \mintinline{Agda}|Quine ϕ|; and to the interpretations of the quine
 isomorphism functions, which are just the identity functions.

\begin{code}
 max-level : Level
 max-level = lzero   ---- also works for higher levels

 mutual
  ⟦_⟧ᶜ : (Γ : Context) → Set (lsuc max-level)
  ⟦ ε ⟧ᶜ  = ⊤
  ⟦ Γ ▻ T ⟧ᶜ = Σ ⟦ Γ ⟧ᶜ ⟦ T ⟧ᵀ

  ⟦_⟧ᵀ : ∀ {Γ}
    → Type Γ → ⟦ Γ ⟧ᶜ → Set max-level
  ⟦ ‘Typeε’ ⟧ᵀ Γ⇓ = Lifted (Type ε)
  ⟦ ‘□’ ⟧ᵀ Γ⇓ = Lifted (Term {ε} (lower (snd Γ⇓)))
  ⟦ Quine ϕ ⟧ᵀ Γ⇓ = ⟦ ϕ ⟧ᵀ (Γ⇓ , lift (Quine ϕ))
  ---- The rest of the type-level interpretations
  ---- are the obvious ones, if a bit obscured by
  ---- carrying around the context.
  ⟦ A ‘→’ B ⟧ᵀ Γ⇓ = ⟦ A ⟧ᵀ Γ⇓ → ⟦ B ⟧ᵀ Γ⇓
  ⟦ ‘⊤’ ⟧ᵀ Γ⇓ = ⊤
  ⟦ ‘⊥’ ⟧ᵀ Γ⇓ = ⊥
  ⟦ W T ⟧ᵀ Γ⇓ = ⟦ T ⟧ᵀ (fst Γ⇓)
  ⟦ W₁ T ⟧ᵀ Γ⇓ = ⟦ T ⟧ᵀ (fst (fst Γ⇓) , snd Γ⇓)
  ⟦ T ‘’ x ⟧ᵀ Γ⇓ = ⟦ T ⟧ᵀ (Γ⇓ , ⟦ x ⟧ᵗ Γ⇓)

  ⟦_⟧ᵗ : ∀ {Γ T}
    → Term {Γ} T → (Γ⇓ : ⟦ Γ ⟧ᶜ) → ⟦ T ⟧ᵀ Γ⇓
  ⟦ ⌜ x ⌝ᵀ ⟧ᵗ Γ⇓ = lift x
  ⟦ ⌜ x ⌝ᵗ ⟧ᵗ Γ⇓ = lift x
  ⟦ quine→ ⟧ᵗ Γ⇓ x = x
  ⟦ quine← ⟧ᵗ Γ⇓ x = x
  ---- The rest of the term-level interpretations
  ---- are the obvious ones, if a bit obscured by
  ---- carrying around the context.
  ⟦ ‘λ’ f ⟧ᵗ Γ⇓ x = ⟦ f ⟧ᵗ (Γ⇓ , x)
  ⟦ ‘tt’ ⟧ᵗ  Γ⇓ = tt
  ⟦ ‘VAR₀’ ⟧ᵗ Γ⇓ = snd Γ⇓
  ⟦ ‘⌜‘VAR₀’⌝ᵗ’ ⟧ᵗ Γ⇓ = lift ⌜ lower (snd Γ⇓) ⌝ᵗ
  ⟦ g ‘∘’ f ⟧ᵗ Γ⇓ x = ⟦ g ⟧ᵗ Γ⇓ (⟦ f ⟧ᵗ Γ⇓ x)
  ⟦ f ‘’ₐ x ⟧ᵗ Γ⇓ = ⟦ f ⟧ᵗ Γ⇓ (⟦ x ⟧ᵗ Γ⇓)
  ⟦ ←SW₁SV→W f ⟧ᵗ = ⟦ f ⟧ᵗ
  ⟦ →SW₁SV→W f ⟧ᵗ = ⟦ f ⟧ᵗ
  ⟦ w x ⟧ᵗ Γ⇓ = ⟦ x ⟧ᵗ (fst Γ⇓)
  ⟦ w→ f ⟧ᵗ Γ⇓ = ⟦ f ⟧ᵗ (fst Γ⇓)
  ⟦ f w‘‘’’ₐ x ⟧ᵗ Γ⇓
    = lift (lower (⟦ f ⟧ᵗ Γ⇓) ‘’ₐ lower (⟦ x ⟧ᵗ Γ⇓))
\end{code}

 To prove Lӧb's theorem, we must create the sentence ``if this
 sentence is provable, then $X$'', and then provide and inhabitant of
 that type.  We can define this sentence, which we call
 \mintinline{Agda}|‘H’|, as the type-level quine at the function
 $\lambda v.\ □ v → ‘X’$.  We can then convert back and forth between
 the types \mintinline{Agda}|□ ‘H’| and \mintinline{Agda}|□ ‘H’ → ‘X’|
 with our quine isomorphism functions, and a bit of quotation magic
 and function application gives us a term of type
 \mintinline{Agda}|□ ‘H’ → □ ‘X’|; this corresponds to the inference
 of the provability of Santa Claus' existence from the assumption that
 the sentence is provable.  We compose this with the assumption of
 Lӧb's theorem, that \mintinline{Agda}|□ ‘X’ → ‘X’|, to get a term of
 type \mintinline{Agda}|□ ‘H’ → ‘X’|, i.e., a term of type
 \mintinline{Agda}|‘H’|; this is the inference that when provability
 implies truth, Santa Claus exists, and hence that the sentence is
 provable.  Finally, we apply this to its own quotation, obtaining a
 term of type \mintinline{Agda}|□ ‘X’|, i.e., a proof that Santa Claus
 exists.

\begin{code}
 module inner (‘X’ : Type ε)
              (‘f’ : Term {ε} (‘□’ ‘’ ⌜ ‘X’ ⌝ᵀ ‘→’ ‘X’))
        where
  ‘H’ : Type ε
  ‘H’ = Quine (W₁ ‘□’ ‘’ ‘VAR₀’ ‘→’ W ‘X’)

  ‘toH’ : □ ((‘□’ ‘’ ⌜ ‘H’ ⌝ᵀ ‘→’ ‘X’) ‘→’ ‘H’)
  ‘toH’ = ←SW₁SV→W quine←

  ‘fromH’ : □ (‘H’ ‘→’ (‘□’ ‘’ ⌜ ‘H’ ⌝ᵀ ‘→’ ‘X’))
  ‘fromH’ = →SW₁SV→W quine→

  ‘□‘H’→□‘X’’ : □ (‘□’ ‘’ ⌜ ‘H’ ⌝ᵀ ‘→’ ‘□’ ‘’ ⌜ ‘X’ ⌝ᵀ)
  ‘□‘H’→□‘X’’
    = ‘λ’ (w ⌜ ‘fromH’ ⌝ᵗ
          w‘‘’’ₐ ‘VAR₀’
          w‘‘’’ₐ ‘⌜‘VAR₀’⌝ᵗ’)

  ‘h’ : Term ‘H’
  ‘h’ = ‘toH’ ‘’ₐ (‘f’ ‘∘’ ‘□‘H’→□‘X’’)

  Lӧb : □ ‘X’
  Lӧb = ‘fromH’ ‘’ₐ ‘h’ ‘’ₐ ⌜ ‘h’ ⌝ᵗ

 Lӧb : ∀ {X} → □ (‘□’ ‘’ ⌜ X ⌝ᵀ ‘→’ X) → □ X
 Lӧb {X} f = inner.Lӧb X f

 ⟦_⟧ : Type ε → Set _
 ⟦ T ⟧ = ⟦ T ⟧ᵀ tt

 ‘¬’_ : ∀ {Γ} → Type Γ → Type Γ
 ‘¬’ T = T ‘→’ ‘⊥’

 lӧb : ∀ {‘X’} → □ (‘□’ ‘’ ⌜ ‘X’ ⌝ᵀ ‘→’ ‘X’) → ⟦ ‘X’ ⟧
 lӧb f = ⟦_⟧ᵗ (Lӧb f) tt
\end{code}

 As above, we can again prove soundness, incompleteness, and non-emptiness.

\begin{code}
 incompleteness : ¬ □ (‘¬’ (‘□’ ‘’ ⌜ ‘⊥’ ⌝ᵀ))
 incompleteness = lӧb

 soundness : ¬ □ ‘⊥’
 soundness x = ⟦ x ⟧ᵗ tt

 non-emptiness : Σ (Type ε) (λ T → □ T)
 non-emptiness = ‘⊤’ , ‘tt’

\end{code}

\section{Digression: Application of Quining to The Prisoner's Dilemma} \label{sec:prisoner}

  In this section, we use a slightly more enriched encoding of syntax;
  see \autoref{sec:prisoners-dilemma-lob-encoding} for details.

\AgdaHide{
  \begin{code}
module prisoners-dilemma where
 open import prisoners-dilemma-lob public
  \end{code}
}

  \subsection{The Prisoner's Dilemma}

    The Prisoner's Dilemma is a classic problem in game theory.  Two
    people have been arrested as suspects in a crime and are being
    held in solatary confinement, with no means of communication.  The
    investigators offer each of them a plea bargain: a decreased
    sentence for ratting out the other person.  Each suspect can then
    choose to either cooperate with the other suspect by remaining
    silent, or defect by ratting out the other suspect.  The possible
    outcomes are summarized in~\autoref{tab:prisoner-payoff}.

\begin{table}
\begin{center}
\begin{tabular}{c|cc}
\backslashbox{$B$ Says}{$A$ Says} & Cooperate & Defect \\ \hline
Cooperate & (1 year, 1 year) & (0 years, 3 years) \\
Defect & (3 years, 0 years) & (2 years, 2 years)
\end{tabular}
\caption{The payoff matrix for the prisoner's dilemma; each cell contains (the years $A$ spends in prison, the years $B$ spends in prison).} \label{tab:prisoner-payoff}
\end{center}
\end{table}

    Suspect $A$ might reason thusly: ``Suppose the other suspect
    cooperates with me.  Then I'd get off with no prison time if I
    defected, while I'd have to spend a year in prison if I cooperate.
    Similarly, if the other suspect defects, then I'd get two years in
    prison for defecting, and three for cooperating.  In all cases, I
    do better by defecting.''  If suspect $B$ reasons similarly, then
    both decide to defect, and both get two years in prison, despite
    the fact that both prefer the (Cooperate, Cooperate) outcome over
    the (Defect, Defect) outcome!

  \subsection{Adding Source Code}

    We have the intuition that if both suspects are good at reasoning,
    and both know that they'll reason the same way, then they should
    be able to mutually cooperate.  One way to formalize this is to
    talk about programs (rather than people) playing the prisoner's
    dilemma, and to allow each program access to its own source code
    and its opponent's source
    code~\cite{BaraszChristianoFallensteinEtAl2014}.

    We have formalized this framework in Agda: we use
    \mintinline{Agda}|‘Bot’| to denote the type of programs that can
    play in such a prisoner's dilemma; each one takes in source code
    for two \mintinline{Agda}|‘Bot’|s and outputs a proposition which
    is true (a type which is inhabited) if and only if it cooperates
    with its opponent.  Said another way, the output of each bot is a
    proposition describing the assertion that it cooperates with its
    opponent.

\begin{code}
 open lob

 ---- ‘Bot’ is defined as the fixed point of
 ---- ‘Bot’
 ----   ↔ (Term ‘Bot’ → Term ‘Bot’ → ‘Type’)
 ‘Bot’ : ∀ {Γ} → Type Γ
 ‘Bot’ {Γ}
   = Quine (W₁ ‘Term’ ‘’ ‘VAR₀’
            ‘→’ W₁ ‘Term’ ‘’ ‘VAR₀’
            ‘→’ W (‘Type’ Γ))
\end{code}

  To construct an executable bot, we could do a bounded search for
  proofs of this proposition; one useful method described in
  \cite{BaraszChristianoFallensteinEtAl2014} is to use Kripke frames.
  This computation is, however, beyond the scope of this paper.

  The assertion that a bot \mintinline{Agda}|b₁| cooperates with a bot
  \mintinline{Agda}|b₂| is the result of interpreting the source code
  for the bot, and feeding the resulting function the source code for
  \mintinline{Agda}|b₁| and \mintinline{Agda}|b₂|.

\begin{code}
 ---- N.B. "□" means "Term {ε}", i.e., a term in
 ---- the empty context
 _cooperates-with_ : □ ‘Bot’ → □ ‘Bot’ → Type ε
 b₁ cooperates-with b₂ = lower (⟦ b₁ ⟧ᵗ tt (lift b₁) (lift b₂))
\end{code}

  We now provide a convenience constructor for building bots, based on
  the definition of quines, and present four relatively simple bots:
  DefectBot, CooperateBot, FairBot, and PrudentBot.

\begin{code}
 make-bot : ∀ {Γ}
   → Term {Γ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)}
          (W (W (‘Type’ Γ)))
   → Term {Γ} ‘Bot’
 make-bot t
   = ←SW₁SV→SW₁SV→W
     quine← ‘’ₐ ‘λ’ (→w (‘λ’ t))

 ‘DefectBot’    : □ ‘Bot’
 ‘CooperateBot’ : □ ‘Bot’
 ‘FairBot’      : □ ‘Bot’
 ‘PrudentBot’   : □ ‘Bot’
\end{code}

  The first two bots are very simple: DefectBot never cooperates (the
  assertion that DefectBot cooperates is a contradiction), while
  CooperateBot always cooperates.  We define these bots, and prove
  that DefectBot never cooperates and CooperateBot always cooperates.

\begin{code}
 ‘DefectBot’    = make-bot (w (w ⌜ ‘⊥’ ⌝ᵀ))
 ‘CooperateBot’ = make-bot (w (w ⌜ ‘⊤’ ⌝ᵀ))

 DB-defects : ∀ {b}
   → ¬ ⟦ ‘DefectBot’ cooperates-with b ⟧
 DB-defects {b} pf = pf

 CB-cooperates : ∀ {b}
   → ⟦ ‘CooperateBot’ cooperates-with b ⟧
 CB-cooperates {b} = tt
\end{code}

  We can do better than DefectBot, though, now that we have source
  code.  FairBot cooperates with you if and only if it can find a
  proof that you cooperate with FairBot.  By Lӧb's theorem, to prove
  that FairBot cooperates with itself, it sufficies to prove that if
  there is a proof that FairBot cooperates with itself, then FairBot
  does, in fact, cooperate with itself.  This is obvious, though:
  FairBot decides whether or not to cooperate with itself by searching
  for a proof that it does, in fact, cooperate with itself.

  To define FairBot, we first define what it means for the other bot
  to cooperate with some particular bot.

\begin{code}
 ---- We can "evaluate" a bot to turn it into a
 ---- function accepting the source code of two
 ---- bots.
 ‘eval-bot’ : ∀ {Γ}
   → Term {Γ} (‘Bot’
              ‘→’ (‘□’ ‘Bot’ ‘→’ ‘□’ ‘Bot’ ‘→’ ‘Type’ Γ))
 ‘eval-bot’ = →SW₁SV→SW₁SV→W quine→

 ---- We can quote this, and get a function that
 ---- takes the source code for a bot, and
 ---- outputs the source code for a function that
 ---- takes (the source code for) that bot's
 ---- opponent, and returns an assertion of
 ---- cooperation with that opponent
 ‘‘eval-bot’’ : ∀ {Γ}
   → Term {Γ} (‘□’ ‘Bot’
     ‘→’ ‘□’ ({- other -} ‘□’ ‘Bot’ ‘→’ ‘Type’ Γ))
 ‘‘eval-bot’’
   = ‘λ’ (w ⌜ ‘eval-bot’ ⌝ᵗ
         w‘‘’’ₐ ‘VAR₀’
         w‘‘’’ₐ ‘⌜‘VAR₀’⌝ᵗ’)

 ---- The assertion "our opponent cooperates with
 ---- a bot b" is equivalent to the evalution of
 ---- our opponent, applied to b.  Most of the
 ---- noise in this statement is manipulation of
 ---- weakening and substiution.
 ‘other-cooperates-with’ : ∀ {Γ}
   → Term {Γ
      ▻ ‘□’ ‘Bot’
      ▻ W (‘□’ ‘Bot’)}
     (W (W (‘□’ ‘Bot’)) ‘→’ W (W (‘□’ (‘Type’ Γ))))
 ‘other-cooperates-with’ {Γ}
   = ‘eval-other'’
     ‘∘’ w→ (w (w→ (w (‘λ’ ‘⌜‘VAR₀’⌝ᵗ’))))
  where
   ‘eval-other’
     : Term {Γ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)}
            (W (W (‘□’ (‘□’ ‘Bot’ ‘→’ ‘Type’ Γ))))
   ‘eval-other’
     = w→ (w (w→ (w ‘‘eval-bot’’))) ‘’ₐ ‘VAR₀’

   ‘eval-other'’
     : Term (W (W (‘□’ (‘□’ ‘Bot’)))
             ‘→’ W (W (‘□’ (‘Type’ Γ))))
   ‘eval-other'’
     = ww→ (w→ (w (w→ (w ‘‘’ₐ’))) ‘’ₐ ‘eval-other’)

 ---- A bot gets its own source code as the first
 ---- argument (of two)
 ‘self’ : ∀ {Γ}
   → Term {Γ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)}
          (W (W (‘□’ ‘Bot’)))
 ‘self’ = w ‘VAR₀’

 ---- A bot gets its opponent's source code as
 ---- the second argument (of two)
 ‘other’ : ∀ {Γ}
   → Term {Γ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)}
          (W (W (‘□’ ‘Bot’)))
 ‘other’ = ‘VAR₀’

 ---- FairBot is the bot that cooperates iff its
 ---- opponent cooperates with it
 ‘FairBot’
   = make-bot (‘‘□’’ (‘other-cooperates-with’ ‘’ₐ ‘self’))
\end{code}

  We leave the proof that this formalization of FairBot cooperates
  with itself as an exercise for the reader. In
  \autoref{sec:fair-bot-self-cooperates}, we present an alternative
  formalization with a simple proof that FairBot cooperates with
  itself, but with no general definition of the type of bots; we
  relegate this code to an appendix so as to not confuse the reader by
  introducing a different way of handling contexts and weakening in
  the middle of this paper.

  We now come to the final bot: PrudentBot.  You do better in the
  prisoner's dilemma if you cooperate whenever that's required for
  mutual cooperation, and you defect whenever your opponent would
  cooperate even if you defected.  PrudentBot formalizes an
  approximation to this intuition: PrudentBot cooperates with you if
  and only if it can prove that you cooperate with it, and it can
  prove that you defect against DefectBot (when it assumes that
  DefectBot does not cooperate with you).

  PrudentBot defects against DefectBot.  Since there is no proof of ⊥,
  PrudentBot does not find a proof that DefectBot cooperates with it,
  and so it will not cooperate with DefectBot.

  By Lӧb's theorem, PrudentBot cooperates with itself.  Under the
  assumption that ⊥ is unprovable, PrudentBot can prove that it
  defects against DefectBot.  If we further assume that PrudentBot can
  find a proof that it cooperates with itself (which we are allowed to
  do when proving the hypothesis of Lӧb's theorem), then PrudentBot
  will, in fact, cooperate with itself.  Hence, by Lӧb's theorem, we
  can prove that PrudentBot will cooperate with itself.

  We leave the formalization of this proof to the reader, and present
  only the definition of PrudentBot.

\begin{code}
 ---- Convenience notation for triply quoted
 ---- negation in a context with at least two
 ---- terms
 ‘“¬”’_ : ∀ {Γ A B}
   → Term {Γ ▻ A ▻ B} (W (W (‘□’ (‘Type’ Γ))))
   → Term {Γ ▻ A ▻ B} (W (W (‘□’ (‘Type’ Γ))))
 ‘“¬”’ T = T ‘“→”’ w (w ⌜ ⌜ ‘⊥’ ⌝ᵀ ⌝ᵗ)

 ---- PrudentBot cooperates if its opponent
 ---- cooperates with PrudentBot, and if, under
 ---- the assumption that ⊥ is unprovable (¬□⊥),
 ---- its opponent does not cooperate with
 ---- DefectBot
 ‘PrudentBot’
   = make-bot (‘‘□’’
      ((‘other-cooperates-with’ ‘’ₐ ‘self’)
        ‘“×”’
       (¬□⊥ ‘“→”’ other-defects-against-DB)))
  where
   other-defects-against-DB
     : Term {_ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)}
            (W (W (‘□’ (‘Type’ _))))
   other-defects-against-DB
     = ‘“¬”’
       (‘other-cooperates-with’
       ‘’ₐ w (w ⌜ ‘DefectBot’ ⌝ᵗ))

   ¬□⊥ : ∀ {Γ A B}
     → Term {Γ ▻ A ▻ B} (W (W (‘□’ (‘Type’ Γ))))
   ¬□⊥ = w (w ⌜ ⌜ ‘¬’ (‘□’ ‘⊥’) ⌝ᵀ ⌝ᵗ)

\end{code}

\section{Encoding with Add-Quote Function} \label{sec:only-add-quote}

  Now we return to our proving of Lӧb's theorem.  Included in the
  artifact for this paper\footnote{In \texttt{lob-build-quine.lagda}.}
  is code that replaces the \mintinline{Agda}|Quine| constructor with
  simpler constructors.  Because the lack of β-reduction in the syntax
  clouds the main points and makes the code rather verbose, we do not
  include the code in the paper, and instead describe the most
  interesting and central points.

  Recall our Python quine from \autoref{sec:python-quine}:
\begin{minted}[gobble=1]{python}
 (lambda T: □ (T % repr(T)) → X)
  ("(lambda T: □ (T %% repr(T)) → X)\n (%s)")
\end{minted}

  To tranlate this into Agda, we need to give a type to
  \mintinline{Agda}|T|. Clearly, \mintinline{Agda}|T| needs to be of
  type \mintinline{Agda}|Type ???| for some context
  \mintinline{Agda}|???|.  Since we need to be able to subsitute
  something into that context, we must have
  \mintinline{Agda}|T : Type (Γ ▻ ???)|, i.e., \mintinline{Agda}|T|
  must be a syntax tree for a type, with a hole in it.

  What's the shape of the thing being subtituted?  Well, it's a syntax
  tree for a type with a hole in it\ldots\space Uh-oh.  Our quine's
  type, na\"ively, is infinite!

  We know of two ways to work around this.  Classical mathematics,
  which uses Gӧdel codes instead of abstract syntax trees, uses an
  untyped representation of proofs.  It's only later in the proof of
  Lӧb's theorem that a notion of a formula being ``well-formed'' is
  introduced.

  Here, we describe an alternate approach.  Rather than giving up
  types all-together, we can ``box'' the type of the hole, to hide it.
  Using \mintinline{Agda}|fst| and \mintinline{Agda}|snd| to denote
  projections from a Σ type, using \mintinline{Agda}|⌜ A ⌝| to denote
  the abstract syntax tree for \mintinline{Agda}|A|,\footnote{Note
  that \mintinline{Agda}|⌜_⌝| would not be a function in the language,
  but a meta-level operation.} and using \mintinline{Agda}|%s| to
  denote the first variable in the context (written as
  \mintinline{Agda}|‘VAR₀’| in previous formalizations above), we can
  write:

  \begin{minted}[gobble=1]{Agda}
 dummy : Type (ε ▻ ⌜Σ Context Type⌝)
 repr : Σ Context Type → Term {ε} ⌜Σ Context Type⌝

 cast-fst
   : Σ Context Type → Type (ε ▻ ⌜Σ Context Type⌝)
 cast-fst (ε ▻ ⌜Σ Context Type⌝ , T) = T
 cast-fst (_ , _) = dummy

 LӧbSentence : Type ε
 LӧbSentence
   = (λ (T : Σ Context Type)
        → □ (cast-fst T % repr T) ‘→’ X)
       ( ε ▻ ⌜Σ Context Type⌝
       , ⌜ (λ (T : Σ Context Type)
              → □ (cast-fst T % repr T) ‘→’ X)
             (%s) ⌝
  \end{minted}

  In this pseudo-Agda code, \mintinline{Agda}|cast-fst| unboxes the
  sentence that it gets, and returns it if it is the right type.
  Since the sentence is, in fact, always the right type, what we do in
  the other cases doesn't matter.

  Summing up, the key ingredients to this construction are:
  \begin{itemize}
    \item
      A type of syntactic terms indexed over a type of syntactic types (and contexts)
    \item
      Decidable equality on syntactic contexts at a particular point (\mintinline{Agda}|Σ Context Type|), with appropriate reduction on equal things
    \item
      Σ types, projections, and appropriate reduction on their projections
    \item
      Function types
    \item
      A function \mintinline{Agda}|repr| which adds a level of quotation to any syntax tree
    \item
      Syntax trees for all of the above
  \end{itemize}

  In any formalization of dependent type theory with all of these
  ingredients, we can prove Lӧb's theorem.

\section{Conclusion} \label{sec:future-work}

  What remains to be done is formalizing Martin-Lӧf type theory
  without assuming \mintinline{Agda}|repr| nor assuming a constructor
  for the type of syntax trees (\mintinline{Agda}|‘Context’|,
  \mintinline{Agda}|‘Type’|, and \mintinline{Agda}|‘Term’| or
  \mintinline{Agda}|‘□’| in our formalizations), and instead support
  inductive types, and construct these things inductively, and by
  folding over the inductive definitions there-in.

  If you take away only three things from this paper, take away these:
  \begin{enumerate}
    \item There will always be some true things which are not possible
      to say, no matter how good you are at talking in type theory
      about type theory.

    \item Giving meaning to syntax in a way that doesn't use cases
      inside cases allows you to talk about when it's okay to add new
      syntax.

    % \todo{Find an Up-Goer Five way to say "syntax" that doesn't give away the game}

    \item If believing in something is enough to make it true, then
      it already is.  Dream big.
  \end{enumerate}

\appendix
\input{./common.tex}
\input{./prisoners-dilemma-lob.tex}
\AgdaHide{
  \begin{code}
import fair-bot-self-cooperates
  \end{code}
}
\input{./fair-bot-self-cooperates.tex}
%\input{./lob-build-quine.tex}
\inputacknowledgements

%\printbibliography
\bibliographystyle{abbrvnat}
\bibliography{lob}

\end{document}
