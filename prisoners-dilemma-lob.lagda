\section{Encoding of \texorpdfstring{L\"ob}{Lӧb}'s Theorem for the Prisoner's Dilemma} \label{sec:prisoners-dilemma-lob-encoding}
\AgdaHide{
  \begin{code}
module prisoners-dilemma-lob where
 open import common
  \end{code}
}
\begin{code}
 module lob where
  infixl 2 _▻_
  infixl 3 _‘’_
  infixr 1 _‘→’_
  infixr 1 _‘‘→’’_
  infixr 1 _‘“→”’_
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
     ‘⊤’ : ∀ {Γ} → Type Γ
     ‘⊥’ : ∀ {Γ} → Type Γ
     _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
     _‘×’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
     ‘Type’ : ∀ Γ → Type Γ
     ‘Term’ : ∀ {Γ} → Type (Γ ▻ ‘Type’ Γ)
     Quine : ∀ {Γ} → Type (Γ ▻ ‘Type’ Γ) → Type Γ
     W : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
     W₁ : ∀ {Γ A B}
       → Type (Γ ▻ B)
       → Type (Γ ▻ A ▻ W B)
     _‘’_ : ∀ {Γ A}
       → Type (Γ ▻ A)
       → Term A
       → Type Γ

   data Term : {Γ : Context} → Type Γ → Set where
     ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
     ‘λ’ : ∀ {Γ A B}
       → Term {Γ ▻ A} (W B)
       → Term (A ‘→’ B)
     ‘VAR₀’ : ∀ {Γ T} → Term {Γ ▻ T} (W T)
     ⌜_⌝ᵀ : ∀ {Γ}
       → Type Γ
       → Term {Γ} (‘Type’ Γ)
     ⌜_⌝ᵗ : ∀ {Γ T}
       → Term {Γ} T
       → Term {Γ} (‘Term’ ‘’ ⌜ T ⌝ᵀ)
     ‘⌜‘VAR₀’⌝ᵗ’ : ∀ {Γ T}
       → Term {Γ ▻ ‘Term’ ‘’ ⌜ T ⌝ᵀ}
              (W (‘Term’ ‘’ ⌜ ‘Term’ ‘’ ⌜ T ⌝ᵀ ⌝ᵀ))
     ‘⌜‘VAR₀’⌝ᵀ’ : ∀ {Γ}
       → Term {Γ ▻ ‘Type’ Γ}
              (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝ᵀ))
     _‘’ₐ_ : ∀ {Γ A B}
       → Term {Γ} (A ‘→’ B)
       → Term {Γ} A
       → Term {Γ} B
     ‘‘×'’’ : ∀ {Γ}
       → Term {Γ} (‘Type’ Γ
                  ‘→’ ‘Type’ Γ
                  ‘→’ ‘Type’ Γ)
     quine→ : ∀ {Γ φ}
       → Term {Γ}
              (Quine φ           ‘→’ φ ‘’ ⌜ Quine φ ⌝ᵀ)
     quine← : ∀ {Γ φ}
       → Term {Γ}
              (φ ‘’ ⌜ Quine φ ⌝ᵀ ‘→’ Quine φ)
     SW : ∀ {Γ X A} {a : Term A}
       → Term {Γ} (W X ‘’ a)
       → Term X
     →SW₁SV→W
       : ∀ {Γ T X A B} {x : Term X}
       → Term {Γ}
              (T ‘→’ (W₁ A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x)
       → Term {Γ}
              (T ‘→’ A ‘’ x ‘→’ B)
     ←SW₁SV→W
       : ∀ {Γ T X A B} {x : Term X}
       → Term {Γ}
              ((W₁ A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x ‘→’ T)
       → Term {Γ}
              ((A ‘’ x ‘→’ B) ‘→’ T)
     →SW₁SV→SW₁SV→W
       : ∀ {Γ T X A B} {x : Term X}
       → Term {Γ} (T ‘→’ (W₁ A ‘’ ‘VAR₀’
                         ‘→’ W₁ A ‘’ ‘VAR₀’
                         ‘→’ W B) ‘’ x)
       → Term {Γ} (T ‘→’ A ‘’ x ‘→’ A ‘’ x ‘→’ B)
     ←SW₁SV→SW₁SV→W
       : ∀ {Γ T X A B} {x : Term X}
       → Term {Γ} ((W₁ A ‘’ ‘VAR₀’
                  ‘→’ W₁ A ‘’ ‘VAR₀’
                  ‘→’ W B) ‘’ x
                  ‘→’ T)
       → Term {Γ} ((A ‘’ x ‘→’ A ‘’ x ‘→’ B) ‘→’ T)
     w : ∀ {Γ A T}
       → Term {Γ} A
       → Term {Γ ▻ T} (W A)
     w→ : ∀ {Γ A B X}
       → Term {Γ ▻ X} (W (A ‘→’ B))
       → Term {Γ ▻ X} (W A ‘→’ W B)
     →w : ∀ {Γ A B X}
       → Term {Γ ▻ X} (W A ‘→’ W B)
       → Term {Γ ▻ X} (W (A ‘→’ B))
     ww→ : ∀ {Γ A B X Y}
       → Term {Γ ▻ X ▻ Y} (W (W (A ‘→’ B)))
       → Term {Γ ▻ X ▻ Y} (W (W A) ‘→’ W (W B))
     →ww : ∀ {Γ A B X Y}
       → Term {Γ ▻ X ▻ Y} (W (W A) ‘→’ W (W B))
       → Term {Γ ▻ X ▻ Y} (W (W (A ‘→’ B)))
     _‘∘’_ : ∀ {Γ A B C}
       → Term {Γ} (B ‘→’ C)
       → Term {Γ} (A ‘→’ B)
       → Term {Γ} (A ‘→’ C)
     _w‘‘’’ₐ_ : ∀ {Γ A B T}
       → Term {Γ ▻ T} (W (‘Term’ ‘’ ⌜ A ‘→’ B ⌝ᵀ))
       → Term {Γ ▻ T} (W (‘Term’ ‘’ ⌜ A ⌝ᵀ))
       → Term {Γ ▻ T} (W (‘Term’ ‘’ ⌜ B ⌝ᵀ))
     ‘‘’ₐ’ : ∀ {Γ A B}
       → Term {Γ} (‘Term’ ‘’ ⌜ A ‘→’ B ⌝ᵀ
                  ‘→’ ‘Term’ ‘’ ⌜ A ⌝ᵀ
                  ‘→’ ‘Term’ ‘’ ⌜ B ⌝ᵀ)
     ‘‘□’’ : ∀ {Γ A B}
       → Term {Γ ▻ A ▻ B}
              (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝ᵀ)))
       → Term {Γ ▻ A ▻ B}
              (W (W (‘Type’ Γ)))
     _‘‘→’’_ : ∀ {Γ}
       → Term {Γ} (‘Type’ Γ)
       → Term {Γ} (‘Type’ Γ)
       → Term {Γ} (‘Type’ Γ)
     _‘“→”’_ : ∀ {Γ A B}
       → Term {Γ ▻ A ▻ B}
              (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝ᵀ)))
       → Term {Γ ▻ A ▻ B}
              (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝ᵀ)))
       → Term {Γ ▻ A ▻ B}
              (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝ᵀ)))
     _‘“×”’_ : ∀ {Γ A B}
       → Term {Γ ▻ A ▻ B}
              (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝ᵀ)))
       → Term {Γ ▻ A ▻ B}
              (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝ᵀ)))
       → Term {Γ ▻ A ▻ B}
              (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝ᵀ)))

  □ : Type ε → Set _
  □ = Term {ε}

  ‘□’ : ∀ {Γ} → Type Γ → Type Γ
  ‘□’ T = ‘Term’ ‘’ ⌜ T ⌝ᵀ

  _‘‘×’’_ : ∀ {Γ}
    → Term {Γ} (‘Type’ Γ)
    → Term {Γ} (‘Type’ Γ)
    → Term {Γ} (‘Type’ Γ)
  A ‘‘×’’ B = ‘‘×'’’ ‘’ₐ A ‘’ₐ B

  max-level : Level
  max-level = lzero

  mutual
   ⟦_⟧ᶜ : (Γ : Context) → Set (lsuc max-level)
   ⟦ ε ⟧ᶜ = ⊤
   ⟦ Γ ▻ T ⟧ᶜ = Σ ⟦ Γ ⟧ᶜ ⟦ T ⟧ᵀ

   ⟦_⟧ᵀ : {Γ : Context}
     → Type Γ
     → ⟦ Γ ⟧ᶜ
     → Set max-level
   ⟦ W T ⟧ᵀ ⟦Γ⟧
     = ⟦ T ⟧ᵀ (Σ.fst ⟦Γ⟧)
   ⟦ W₁ T ⟧ᵀ ⟦Γ⟧
     = ⟦ T ⟧ᵀ (Σ.fst (Σ.fst ⟦Γ⟧) , Σ.snd ⟦Γ⟧)
   ⟦ T ‘’ x ⟧ᵀ ⟦Γ⟧ = ⟦ T ⟧ᵀ (⟦Γ⟧ , ⟦ x ⟧ᵗ ⟦Γ⟧)
   ⟦ ‘Type’ Γ ⟧ᵀ ⟦Γ⟧
     = Lifted (Type Γ)
   ⟦ ‘Term’ ⟧ᵀ ⟦Γ⟧
     = Lifted (Term (lower (Σ.snd ⟦Γ⟧)))
   ⟦ A ‘→’ B ⟧ᵀ ⟦Γ⟧ = ⟦ A ⟧ᵀ ⟦Γ⟧ → ⟦ B ⟧ᵀ ⟦Γ⟧
   ⟦ A ‘×’ B ⟧ᵀ ⟦Γ⟧ = ⟦ A ⟧ᵀ ⟦Γ⟧ × ⟦ B ⟧ᵀ ⟦Γ⟧
   ⟦ ‘⊤’ ⟧ᵀ ⟦Γ⟧ = ⊤
   ⟦ ‘⊥’ ⟧ᵀ ⟦Γ⟧ = ⊥
   ⟦ Quine φ ⟧ᵀ ⟦Γ⟧ = ⟦ φ ⟧ᵀ (⟦Γ⟧ , (lift (Quine φ)))

   ⟦_⟧ᵗ : ∀ {Γ : Context} {T : Type Γ}
     → Term T
     → (⟦Γ⟧ : ⟦ Γ ⟧ᶜ)
     → ⟦ T ⟧ᵀ ⟦Γ⟧
   ⟦ ⌜ x ⌝ᵀ ⟧ᵗ ⟦Γ⟧ = lift x
   ⟦ ⌜ x ⌝ᵗ ⟧ᵗ ⟦Γ⟧ = lift x
   ⟦ ‘⌜‘VAR₀’⌝ᵗ’ ⟧ᵗ ⟦Γ⟧
     = lift ⌜ lower (Σ.snd ⟦Γ⟧) ⌝ᵗ
   ⟦ ‘⌜‘VAR₀’⌝ᵀ’ ⟧ᵗ ⟦Γ⟧
     = lift ⌜ lower (Σ.snd ⟦Γ⟧) ⌝ᵀ
   ⟦ f ‘’ₐ x ⟧ᵗ ⟦Γ⟧ = ⟦ f ⟧ᵗ ⟦Γ⟧ (⟦ x ⟧ᵗ ⟦Γ⟧)
   ⟦ ‘tt’ ⟧ᵗ ⟦Γ⟧ = tt
   ⟦ quine→ {φ} ⟧ᵗ ⟦Γ⟧ x = x
   ⟦ quine← {φ} ⟧ᵗ ⟦Γ⟧ x = x
   ⟦ ‘λ’ f ⟧ᵗ ⟦Γ⟧ x = ⟦ f ⟧ᵗ (⟦Γ⟧ , x)
   ⟦ ‘VAR₀’ ⟧ᵗ ⟦Γ⟧ = Σ.snd ⟦Γ⟧
   ⟦ SW t ⟧ᵗ = ⟦ t ⟧ᵗ
   ⟦ ←SW₁SV→W f ⟧ᵗ = ⟦ f ⟧ᵗ
   ⟦ →SW₁SV→W f ⟧ᵗ = ⟦ f ⟧ᵗ
   ⟦ ←SW₁SV→SW₁SV→W f ⟧ᵗ = ⟦ f ⟧ᵗ
   ⟦ →SW₁SV→SW₁SV→W f ⟧ᵗ = ⟦ f ⟧ᵗ
   ⟦ w x ⟧ᵗ ⟦Γ⟧ = ⟦ x ⟧ᵗ (Σ.fst ⟦Γ⟧)
   ⟦ w→ f ⟧ᵗ ⟦Γ⟧ = ⟦ f ⟧ᵗ ⟦Γ⟧
   ⟦ →w f ⟧ᵗ ⟦Γ⟧ = ⟦ f ⟧ᵗ ⟦Γ⟧
   ⟦ ww→ f ⟧ᵗ ⟦Γ⟧ = ⟦ f ⟧ᵗ ⟦Γ⟧
   ⟦ →ww f ⟧ᵗ ⟦Γ⟧ = ⟦ f ⟧ᵗ ⟦Γ⟧
   ⟦ ‘‘×'’’ ⟧ᵗ ⟦Γ⟧ A B = lift (lower A ‘×’ lower B)
   ⟦ g ‘∘’ f ⟧ᵗ ⟦Γ⟧ x = ⟦ g ⟧ᵗ ⟦Γ⟧ (⟦ f ⟧ᵗ ⟦Γ⟧ x)
   ⟦ f w‘‘’’ₐ x ⟧ᵗ ⟦Γ⟧
     = lift (lower (⟦ f ⟧ᵗ ⟦Γ⟧) ‘’ₐ lower (⟦ x ⟧ᵗ ⟦Γ⟧))
   ⟦ ‘‘’ₐ’ ⟧ᵗ ⟦Γ⟧ f x
     = lift (lower f ‘’ₐ lower x)
   ⟦ ‘‘□’’ {Γ} T ⟧ᵗ ⟦Γ⟧
     = lift (‘Term’ ‘’ lower (⟦ T ⟧ᵗ ⟦Γ⟧))
   ⟦ A ‘‘→’’ B ⟧ᵗ ⟦Γ⟧
     = lift
       (lower (⟦ A ⟧ᵗ ⟦Γ⟧) ‘→’ lower (⟦ B ⟧ᵗ ⟦Γ⟧))
   ⟦ A ‘“→”’ B ⟧ᵗ ⟦Γ⟧
     = lift
       (lower (⟦ A ⟧ᵗ ⟦Γ⟧) ‘‘→’’ lower (⟦ B ⟧ᵗ ⟦Γ⟧))
   ⟦ A ‘“×”’ B ⟧ᵗ ⟦Γ⟧
     = lift
       (lower (⟦ A ⟧ᵗ ⟦Γ⟧) ‘‘×’’ lower (⟦ B ⟧ᵗ ⟦Γ⟧))


  module inner (‘X’ : Type ε)
               (‘f’ : Term {ε} (‘□’ ‘X’ ‘→’ ‘X’))
         where
   ‘H’ : Type ε
   ‘H’ = Quine (W₁ ‘Term’ ‘’ ‘VAR₀’ ‘→’ W ‘X’)

   ‘toH’ : □ ((‘□’ ‘H’ ‘→’ ‘X’) ‘→’ ‘H’)
   ‘toH’ = ←SW₁SV→W quine←

   ‘fromH’ : □ (‘H’ ‘→’ (‘□’ ‘H’ ‘→’ ‘X’))
   ‘fromH’ = →SW₁SV→W quine→

   ‘□‘H’→□‘X’’ : □ (‘□’ ‘H’ ‘→’ ‘□’ ‘X’)
   ‘□‘H’→□‘X’’
     = ‘λ’ (w ⌜ ‘fromH’ ⌝ᵗ
           w‘‘’’ₐ ‘VAR₀’
           w‘‘’’ₐ ‘⌜‘VAR₀’⌝ᵗ’)

   ‘h’ : Term ‘H’
   ‘h’ = ‘toH’ ‘’ₐ (‘f’ ‘∘’ ‘□‘H’→□‘X’’)

   Lӧb : □ ‘X’
   Lӧb = ‘fromH’ ‘’ₐ ‘h’ ‘’ₐ ⌜ ‘h’ ⌝ᵗ

  Lӧb : ∀ {X}
    → Term {ε} (‘□’ X ‘→’ X) → Term {ε} X
  Lӧb {X} f = inner.Lӧb X f

  ⟦_⟧ : Type ε → Set _
  ⟦ T ⟧ = ⟦ T ⟧ᵀ tt

  ‘¬’_ : ∀ {Γ} → Type Γ → Type Γ
  ‘¬’ T = T ‘→’ ‘⊥’

  _w‘‘×’’_ : ∀ {Γ X}
    → Term {Γ ▻ X} (W (‘Type’ Γ))
    → Term {Γ ▻ X} (W (‘Type’ Γ))
    → Term {Γ ▻ X} (W (‘Type’ Γ))
  A w‘‘×’’ B = w→ (w→ (w ‘‘×'’’) ‘’ₐ A) ‘’ₐ B

  lӧb : ∀ {‘X’} → □ (‘□’ ‘X’ ‘→’ ‘X’) → ⟦ ‘X’ ⟧
  lӧb f = ⟦ Lӧb f ⟧ᵗ tt

  incompleteness : ¬ □ (‘¬’ (‘□’ ‘⊥’))
  incompleteness = lӧb

  soundness : ¬ □ ‘⊥’
  soundness x = ⟦ x ⟧ᵗ tt

  non-emptiness : Σ (Type ε) (λ T → □ T)
  non-emptiness = ‘⊤’ , ‘tt’
\end{code}
