\section{Encoding with Add-Quote Function}

\AgdaHide{
  \begin{code}
module lob-build-quine where
open import lob
  \end{code}
}


\begin{code}
module lob-by-repr where
 module well-typed-syntax where

  infixl 1 _‘,’_
  infixl 2 _▻_
  infixl 3 _‘’_
  infixl 3 _‘’₁_
  infixl 3 _‘’₂_
  infixl 3 _‘’₃_
  infixl 3 _‘’ₐ_
  infixr 1 _‘→’_
  infixl 3 _‘‘’’_
  infixl 3 _w‘‘’’_
  infixr 1 _‘‘→'’’_
  infixr 1 _w‘‘→'’’_

  mutual
   data Context : Set where
    ε : Context
    _▻_ : (Γ : Context) → Type Γ → Context

   data Type : Context → Set where
    _‘→’_ : ∀ {Γ} (A : Type Γ) → Type (Γ ▻ A) → Type Γ
    ‘Σ’ : ∀ {Γ} (T : Type Γ) → Type (Γ ▻ T) → Type Γ
    ‘Context’ : ∀ {Γ} → Type Γ
    ‘Type’ : ∀ {Γ} → Type (Γ ▻ ‘Context’)
    ‘Term’ : ∀ {Γ} → Type (Γ ▻ ‘Context’ ▻ ‘Type’)
    _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term A → Type Γ
    _‘’₁_ : ∀ {Γ A B} → (C : Type (Γ ▻ A ▻ B)) → (a : Term A) → Type (Γ ▻ B ‘’ a)
    _‘’₂_ : ∀ {Γ A B C} → (D : Type (Γ ▻ A ▻ B ▻ C)) → (a : Term A) → Type (Γ ▻ B ‘’ a ▻ C ‘’₁ a)
    _‘’₃_ : ∀ {Γ A B C D} → (E : Type (Γ ▻ A ▻ B ▻ C ▻ D)) → (a : Term A) → Type (Γ ▻ B ‘’ a ▻ C ‘’₁ a ▻ D ‘’₂ a)
    W : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
    W₁ : ∀ {Γ A B} → Type (Γ ▻ B) → Type (Γ ▻ A ▻ (W {Γ} {A} B))
    W₂ : ∀ {Γ A B C} → Type (Γ ▻ B ▻ C) → Type (Γ ▻ A ▻ W B ▻ W₁ C)

   data Term : ∀ {Γ} → Type Γ → Set where
    w : ∀ {Γ A B} → Term {Γ} B → Term {Γ ▻ A} (W {Γ} {A} B)
    ‘λ’ : ∀ {Γ A B} → Term {(Γ ▻ A)} B → Term {Γ} (A ‘→’ B)
    _‘’ₐ_ : ∀ {Γ A B} → (f : Term {Γ} (A ‘→’ B)) → (x : Term {Γ} A) → Term {Γ} (B ‘’ x)
    ‘VAR₀’ : ∀ {Γ T} → Term {Γ ▻ T} (W T)
    ⌜_⌝ᶜ : ∀ {Γ} → Context → Term {Γ} ‘Context’
    ⌜_⌝ᵀ : ∀ {Γ Γ'} → Type Γ' → Term {Γ} (‘Type’ ‘’ ⌜ Γ' ⌝ᶜ)
    ⌜_⌝ᵗ : ∀ {Γ Γ'} {T : Type Γ'} → Term T → Term {Γ} (‘Term’ ‘’₁ ⌜ Γ' ⌝ᶜ ‘’ ⌜ T ⌝ᵀ)
    ‘⌜_⌝ᵗ’ : ∀ {Γ Γ'} {A : Type Γ'} → Term {Γ} (‘Term’ ‘’₁ ⌜ Γ' ⌝ᶜ ‘’ ⌜ A ⌝ᵀ ‘→’ W (‘Term’ ‘’₁ ⌜ Γ ⌝ᶜ ‘’ ⌜ ‘Term’ ‘’₁ ⌜ Γ' ⌝ᶜ ‘’ ⌜ A ⌝ᵀ ⌝ᵀ))
    ‘quote-Σ’ : ∀ {Γ Γ'} → Term {Γ} (‘Σ’ ‘Context’ ‘Type’ ‘→’ W (‘Term’ ‘’₁ ⌜ Γ' ⌝ᶜ ‘’ ⌜ ‘Σ’ ‘Context’ ‘Type’ ⌝ᵀ))
    ‘cast’ : Term {ε} (‘Σ’ ‘Context’ ‘Type’ ‘→’ W (‘Type’ ‘’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ))
    SW : ∀ {Γ A B} {a : Term {Γ} A} → Term {Γ} (W B ‘’ a) → Term {Γ} B
    WS∀ : ∀ {Γ T T' A B} {a : Term {Γ} T} → Term {Γ ▻ T'} (W ((A ‘→’ B) ‘’ a)) → Term {Γ ▻ T'} (W ((A ‘’ a) ‘→’ (B ‘’₁ a)))
    SW₁V : ∀ {Γ A T} → Term {Γ ▻ A} (W₁ T ‘’ ‘VAR₀’) → Term {Γ ▻ A} T
    W∀ : ∀ {Γ A B C} → Term {Γ ▻ C} (W (A ‘→’ B)) → Term {Γ ▻ C} (W A ‘→’ W₁ B)
    W∀⁻¹ : ∀ {Γ A B C} → Term {Γ ▻ C} (W A ‘→’ W₁ B) → Term {Γ ▻ C} (W (A ‘→’ B))
    WW∀ : ∀ {Γ A B C D} → Term {Γ ▻ C ▻ D} (W (W (A ‘→’ B))) → Term {Γ ▻ C ▻ D} (W (W A ‘→’ W₁ B))
    S₁∀ : ∀ {Γ T T' A B} {a : Term {Γ} T} → Term {Γ ▻ T' ‘’ a} ((A ‘→’ B) ‘’₁ a) → Term {Γ ▻ T' ‘’ a} ((A ‘’₁ a) ‘→’ (B ‘’₂ a))
    S₁₀W⁻¹ : ∀ {Γ C T A} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ} (A ‘’ a) → Term {Γ} (W A ‘’₁ a ‘’ b)
    S₁₀W : ∀ {Γ C T A} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ} (W A ‘’₁ a ‘’ b) → Term {Γ} (A ‘’ a)
    WWS₁₀W : ∀ {Γ C T A D E} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ ▻ D ▻ E} (W (W (W A ‘’₁ a ‘’ b))) → Term {Γ ▻ D ▻ E} (W (W (A ‘’ a)))
    WS₂₁₀W⁻¹ : ∀ {Γ A B C T T'} {a : Term {Γ} A} {b : Term {Γ} (B ‘’ a)} {c : Term {Γ} (C ‘’₁ a ‘’ b)}
      → Term {Γ ▻ T'} (W (T ‘’₁ a ‘’ b))
      → Term {Γ ▻ T'} (W (W T ‘’₂ a ‘’₁ b ‘’ c))
    S₂₁₀W : ∀ {Γ A B C T} {a : Term {Γ} A} {b : Term {Γ} (B ‘’ a)} {c : Term {Γ} (C ‘’₁ a ‘’ b)}
      → Term {Γ} (W T ‘’₂ a ‘’₁ b ‘’ c)
      → Term {Γ} (T ‘’₁ a ‘’ b)
    W₁₀ : ∀ {Γ A B C} → Term {Γ ▻ A ▻ W B} (W₁ (W C)) → Term {Γ ▻ A ▻ W B} (W (W C))
    W₁₀⁻¹ : ∀ {Γ A B C} → Term {Γ ▻ A ▻ W B} (W (W C)) → Term {Γ ▻ A ▻ W B} (W₁ (W C))
    W₁₀₁₀ : ∀ {Γ A B C T} → Term {Γ ▻ A ▻ B ▻ W (W C)} (W₁ (W₁ (W T))) → Term {Γ ▻ A ▻ B ▻ W (W C)} (W₁ (W (W T)))
    S₁W₁ : ∀ {Γ A B C} {a : Term {Γ} A} → Term {Γ ▻ W B ‘’ a} (W₁ C ‘’₁ a) → Term {Γ ▻ B} C
    W₁SW₁⁻¹ : ∀ {Γ A T'' T' T} {a : Term {Γ} A}
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W₁ (W (T ‘’ a)))
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W₁ (W T ‘’₁ a))
    W₁SW₁ : ∀ {Γ A T'' T' T} {a : Term {Γ} A}
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W₁ (W T ‘’₁ a))
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W₁ (W (T ‘’ a)))
    WSSW₁ : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Type (Γ ▻ A)}
      → Term {Γ ▻ T'} (W (W₁ T ‘’ a ‘’ b))
      → Term {Γ ▻ T'} (W (T ‘’ (SW ((‘λ’ a) ‘’ₐ b))))
    WSSW₁⁻¹ : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Type (Γ ▻ A)}
      → Term {Γ ▻ T'} (W (T ‘’ (SW ((‘λ’ a) ‘’ₐ b))))
      → Term {Γ ▻ T'} (W (W₁ T ‘’ a ‘’ b))
    SW₁₀ : ∀ {Γ T} {A : Type Γ} {B : Type Γ}
      → {a : Term {Γ ▻ T} (W {Γ} {T} B)}
      → Term {Γ ▻ T} (W₁ (W A) ‘’ a)
      → Term {Γ ▻ T} (W A)
    WS₂₁₀W₁ : ∀ {Γ A B C T T'} {a : Term {Γ} A} {b : Term (B ‘’ a)} {c : Term (C ‘’ a)}
      → Term {(Γ ▻ T')} (W (W₁ T ‘’₂ a ‘’₁ b ‘’ S₁₀W⁻¹ c))
      → Term {(Γ ▻ T')} (W (T ‘’₁ a ‘’ c))
    S₁₀∀ : ∀ {Γ T T' A B a b} → Term ((_‘→’_ {Γ ▻ T ▻ T'} A B) ‘’₁ a ‘’ b) → Term (_‘→’_ {Γ} (A ‘’₁ a ‘’ b) (B ‘’₂ a ‘’₁ b))
    S₂₀₀W₁₀₀ : ∀ {Γ A} {T : Type (Γ ▻ A)} {T' C B} {a : Term {Γ} A} {b : Term {(Γ ▻ C ‘’ a)} (B ‘’₁ a)}
         {c : Term {(Γ ▻ T')} (W (C ‘’ a))}
         → Term {(Γ ▻ T')} (W₁ (W (W T) ‘’₂ a ‘’ b) ‘’ c)
         → Term {(Γ ▻ T')} (W (T ‘’ a))
    S₁₀W₂₀ : ∀ {Γ T' A B T} {a : Term {Γ ▻ T'} (W A)} {b : Term {Γ ▻ T'} (W₁ B ‘’ a)}
      → Term {Γ ▻ T'} (W₂ (W T) ‘’₁ a ‘’ b)
      → Term {Γ ▻ T'} (W₁ T ‘’ a)
    W₀₁₀ : ∀ {Γ A B C D} → Term {Γ ▻ A ▻ W B ▻ W₁ C} (W (W₁ (W D))) → Term {Γ ▻ A ▻ W B ▻ W₁ C} (W (W (W D)))
    β-under-S : ∀ {Γ A B B'} {g : Term {Γ} (A ‘→’ W B)} {x : Term {Γ} A}
      → Term (B' ‘’ SW (‘λ’ (SW (‘λ’ (W₁₀ (SW₁V (W∀ (w (W∀ (w g))) ‘’ₐ ‘VAR₀’))) ‘’ₐ ‘VAR₀’)) ‘’ₐ x))
      → Term (B' ‘’ SW (g ‘’ₐ x))
    ‘fst'’ : ∀ {Γ} {T : Type Γ} {P : Type (Γ ▻ T)} → Term (‘Σ’ T P ‘→’ W T)
    ‘snd'’ : ∀ {Γ} {T : Type Γ} {P : Type (Γ ▻ T)} → Term {Γ ▻ ‘Σ’ T P} (W₁ P ‘’ SW (‘λ’ (W₁₀ (SW₁V (W∀ (w (W∀ (w ‘fst'’))) ‘’ₐ ‘VAR₀’))) ‘’ₐ ‘VAR₀’))
    _‘,’_ : ∀ {Γ T P} (x : Term {Γ} T) (p : Term (P ‘’ x)) → Term (‘Σ’ T P)
    {- these are redundant, but useful for not having to normalize the subsequent ones -}
    _‘‘’’_ : ∀ {Γ} {A : Type Γ}
      → Term {ε} (‘Type’ ‘’ ⌜ Γ ▻ A ⌝ᶜ)
      → Term {ε} (‘Term’ ‘’₁ ⌜ Γ ⌝ᶜ ‘’ ⌜ A ⌝ᵀ)
      → Term {ε} (‘Type’ ‘’ ⌜ Γ ⌝ᶜ)
    _w‘‘’’_ : ∀ {X Γ} {A : Type Γ}
      → Term {ε ▻ X} (W (‘Type’ ‘’ ⌜ Γ ▻ A ⌝ᶜ))
      → Term {ε ▻ X} (W (‘Term’ ‘’₁ ⌜ Γ ⌝ᶜ ‘’ ⌜ A ⌝ᵀ))
      → Term {ε ▻ X} (W (‘Type’ ‘’ ⌜ Γ ⌝ᶜ))
    _‘‘→'’’_ : ∀ {Γ}
      → Term {ε} (‘Type’ ‘’ Γ)
      → Term {ε} (‘Type’ ‘’ Γ)
      → Term {ε} (‘Type’ ‘’ Γ)
    _w‘‘→'’’_ : ∀ {X Γ}
      → Term {ε ▻ X} (W (‘Type’ ‘’ Γ))
      → Term {ε ▻ X} (W (‘Type’ ‘’ Γ))
      → Term {ε ▻ X} (W (‘Type’ ‘’ Γ))
    w→ : ∀ {Γ A B C} → Term (A ‘→’ W B) → Term {Γ ▻ C} (W A ‘→’ W (W B))
    {- things that were postulates, but are no longer -}
    ‘‘→'’’→w‘‘→'’’ : ∀ {T'}
         {b : Term {ε} (‘Type’ ‘’ ⌜ ε ⌝ᶜ)}
         {c : Term {ε ▻ T'} (W (‘Type’ ‘’ ⌜ ε ⌝ᶜ))}
         {e : Term {ε} T'}
         → Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’ (SW (‘λ’ (c w‘‘→'’’ w b) ‘’ₐ e))
                    ‘→’ W (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’ (SW (‘λ’ c ‘’ₐ e) ‘‘→'’’ b)))
    w‘‘→'’’→‘‘→'’’ : ∀ {T'}
         {b : Term {ε} (‘Type’ ‘’ ⌜ ε ⌝ᶜ)}
         {c : Term {ε ▻ T'} (W (‘Type’ ‘’ ⌜ ε ⌝ᶜ))}
         {e : Term {ε} T'}
         → Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’ (SW (‘λ’ c ‘’ₐ e) ‘‘→'’’ b)
                    ‘→’ W (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’ (SW (‘λ’ (c w‘‘→'’’ w b) ‘’ₐ e))))
    ‘tApp-nd’ : ∀ {Γ} {A : Term {ε} (‘Type’ ‘’ Γ)} {B : Term {ε} (‘Type’ ‘’ Γ)} →
      Term {ε} (‘Term’ ‘’₁ Γ ‘’ (A ‘‘→'’’ B)
           ‘→’ W (‘Term’ ‘’₁ Γ ‘’ A
           ‘→’ W (‘Term’ ‘’₁ Γ ‘’ B)))
    ⌜←'⌝ : ∀ {H X} →
      Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’ (⌜ H ⌝ᵀ ‘‘→'’’ ⌜ X ⌝ᵀ)
           ‘→’ W (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’ ⌜ H ‘→’ W X ⌝ᵀ))
    ⌜→'⌝ : ∀ {H X} →
      Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’ ⌜ H ‘→’ W X ⌝ᵀ
           ‘→’ W (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’ (⌜ H ⌝ᵀ ‘‘→'’’ ⌜ X ⌝ᵀ)))
    ‘‘∘-nd’’ : ∀ {A B C} →
      Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’ (A ‘‘→'’’ C)
           ‘→’ W (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’ (C ‘‘→'’’ B)
           ‘→’ W (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’ (A ‘‘→'’’ B))))
    ⌜‘’⌝ : ∀ {B A} {b : Term {ε} B} →
        Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’
            (⌜ A ‘’ b ⌝ᵀ ‘‘→'’’ ⌜ A ⌝ᵀ ‘‘’’ ⌜ b ⌝ᵗ))
    ⌜‘’⌝' : ∀ {B A} {b : Term {ε} B} →
        Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’
            (⌜ A ⌝ᵀ ‘‘’’ ⌜ b ⌝ᵗ ‘‘→'’’ ⌜ A ‘’ b ⌝ᵀ))
    ‘cast-refl’ : ∀ {T : Type (ε ▻ ‘Σ’ ‘Context’ ‘Type’)} →
        Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’
            ((⌜ T ‘’ _‘,’_ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ ⌝ᵀ)
               ‘‘→'’’
               (SW (‘cast’ ‘’ₐ _‘,’_ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ)
                 ‘‘’’ SW (‘quote-Σ’ ‘’ₐ _‘,’_ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ))))
    ‘cast-refl'’ : ∀ {T : Type (ε ▻ ‘Σ’ ‘Context’ ‘Type’)} →
        Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’
            ((SW (‘cast’ ‘’ₐ _‘,’_ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ)
                 ‘‘’’ SW (‘quote-Σ’ ‘’ₐ _‘,’_ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ))
               ‘‘→'’’
               (⌜ T ‘’ _‘,’_ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ ⌝ᵀ)))
    ‘s→→’ : ∀ {T B}
           {b : Term {ε} (T ‘→’ W (‘Type’ ‘’ ⌜ ε ▻ B ⌝ᶜ))}
           {c : Term {ε} (T ‘→’ W (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’ ⌜ B ⌝ᵀ))}
           {v : Term {ε} T} →
      (Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ
           ‘’ ((SW (((‘λ’ (SW (w→ b ‘’ₐ ‘VAR₀’) w‘‘’’ SW (w→ c ‘’ₐ ‘VAR₀’)) ‘’ₐ v))))
                 ‘‘→'’’ (SW (b ‘’ₐ v) ‘‘’’ SW (c ‘’ₐ v)))))
    ‘s←←’ : ∀ {T B}
           {b : Term {ε} (T ‘→’ W (‘Type’ ‘’ ⌜ ε ▻ B ⌝ᶜ))}
           {c : Term {ε} (T ‘→’ W (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’ ⌜ B ⌝ᵀ))}
           {v : Term {ε} T} →
      (Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ
           ‘’ ((SW (b ‘’ₐ v) ‘‘’’ SW (c ‘’ₐ v))
                 ‘‘→'’’ (SW (((‘λ’ (SW (w→ b ‘’ₐ ‘VAR₀’) w‘‘’’ SW (w→ c ‘’ₐ ‘VAR₀’)) ‘’ₐ v)))))))

\end{code}

\begin{code}
 module well-typed-syntax-helpers where
  open well-typed-syntax

  infixl 3 _‘'’ₐ_
  infixr 1 _‘→'’_
  infixl 3 _‘’ᵗ_
  infixl 3 _‘’ᵗ₁_
  infixl 3 _‘’ᵗ₂_
  infixr 2 _‘∘’_

  _‘→'’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
  _‘→'’_ {Γ} A B = _‘→’_ {Γ} A (W {Γ} {A} B)

  _‘'’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→'’ B) → Term A → Term B
  _‘'’ₐ_ {Γ} {A} {B} f x = SW (_‘’ₐ_ {Γ} {A} {W B} f x)

  _‘’ᵗ_ : ∀ {Γ A} {B : Type (Γ ▻ A)} → (b : Term {Γ ▻ A} B) → (a : Term {Γ} A) → Term {Γ} (B ‘’ a)
  b ‘’ᵗ a = ‘λ’ b ‘’ₐ a

  S∀ : ∀ {Γ T A B} {a : Term {Γ} T} →
                           Term {Γ} ((A ‘→’ B) ‘’ a)
                           → Term {Γ} (_‘→’_ {Γ} (A ‘’ a) (B ‘’₁ a))
  S∀ {Γ} {T} {A} {B} {a} x = SW ((WS∀ (w x)) ‘’ᵗ a)

  ‘λ'∙’ : ∀ {Γ A B} → Term {Γ ▻ A} (W B) -> Term (A ‘→'’ B)
  ‘λ'∙’ f = ‘λ’ f

  un‘λ’ : ∀ {Γ A B} → Term (A ‘→’ B) → Term {Γ ▻ A} B
  un‘λ’ f = SW₁V (W∀ (w f) ‘’ₐ ‘VAR₀’)

  w∀ : ∀ {Γ A B C} →
                            Term {Γ} (A ‘→’ B)
                            → Term {Γ ▻ C} (W A ‘→’ W₁ B)
  w∀ {Γ} {A} {B} {C} x = W∀ (w x)

  w₁ : ∀ {Γ A B C} → Term {Γ ▻ B} C → Term {Γ ▻ A ▻ W {Γ} {A} B} (W₁ {Γ} {A} {B = B} C)
  w₁ x = un‘λ’ (W∀ (w (‘λ’ x)))

  _‘’ᵗ₁_ : ∀ {Γ A B C} → (c : Term {Γ ▻ A ▻ B} C) → (a : Term {Γ} A) → Term {Γ ▻ B ‘’ a} (C ‘’₁ a)
  f ‘’ᵗ₁ x = un‘λ’ (S∀ (‘λ’ (‘λ’ f) ‘’ₐ x))
  _‘’ᵗ₂_ : ∀ {Γ A B C D} → (c : Term {Γ ▻ A ▻ B ▻ C} D) → (a : Term {Γ} A) → Term {Γ ▻ B ‘’ a ▻ C ‘’₁ a} (D ‘’₂ a)
  f ‘’ᵗ₂ x = un‘λ’ (S₁∀ (un‘λ’ (S∀ (‘λ’ (‘λ’ (‘λ’ f)) ‘’ₐ x))))

  S₁₀WW : ∀ {Γ T A} {B : Type (Γ ▻ A)}
      → {a : Term {Γ} A}
      → {b : Term {Γ} (B ‘’ a)}
      → Term {Γ} (W (W T) ‘’₁ a ‘’ b)
      → Term {Γ} T
  S₁₀WW x = SW (S₁₀W x)


  S₂₁₀WW : ∀ {Γ A B C T}
           {a : Term {Γ} A}
           {b : Term {Γ} (B ‘’ a)}
           {c : Term {Γ} (C ‘’₁ a ‘’ b)} →
      Term {Γ} (W (W T) ‘’₂ a ‘’₁ b ‘’ c)
      → Term {Γ} (T ‘’ a)
  S₂₁₀WW x = S₁₀W (S₂₁₀W x)

  W₁₀₁W : ∀ {Γ A B C T} → Term {Γ ▻ A ▻ B ▻ W (W C)} (W₁ (W₁ (W T))) → Term {Γ ▻ A ▻ B ▻ W (W C)} (W₁ (W (W T)))
  W₁₀₁W = W₁₀₁₀

  W∀-nd : ∀ {Γ A B C} →
                            Term {Γ ▻ C} (W (A ‘→'’ B))
                            → Term {Γ ▻ C} (W A ‘→'’ W B)
  W∀-nd x = ‘λ'∙’ (W₁₀ (SW₁V (W∀ (w (W∀ x)) ‘’ₐ ‘VAR₀’)))

  w∀-nd : ∀ {Γ A B C} →
                               Term (A ‘→'’ B)
                               → Term {Γ ▻ C} (W A ‘→'’ W B)
  w∀-nd {Γ} {A} {B} {C} x = W∀-nd (w x)




  W∀-nd-∀-nd : ∀ {Γ A B C D} →
      Term {Γ ▻ D} (W (A ‘→'’ B ‘→'’ C))
      → Term {Γ ▻ D} (W A ‘→'’ W B ‘→'’ W C)
  W∀-nd-∀-nd x = ‘λ’ (W∀⁻¹ (‘λ’ (W₁₀₁W (SW₁V (w∀ (W∀ (WW∀ (w→ (W∀-nd x) ‘'’ₐ ‘VAR₀’))) ‘’ₐ ‘VAR₀’)))))

  w→→ : ∀ {Γ A B C D} →
      Term (A ‘→'’ B ‘→'’ C)
      → Term {Γ ▻ D} (W A ‘→'’ W B ‘→'’ W C)
  w→→ {Γ} {A} {B} {C} {D} x = W∀-nd-∀-nd (w x)

  W₁S₁W⁻¹ : ∀ {Γ A T'' T' T} {a : Term {Γ} A}
        → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W₁ (W (T ‘’ a)))
        → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W₁ (W T ‘’₁ a))
  W₁S₁W⁻¹ = W₁SW₁⁻¹


  SW₁⁻¹ : ∀ {Γ A T' T}
           {a : Term {Γ} A} →
      Term {(Γ ▻ T' ‘’ a)} (W (T ‘’ a))
      → Term {(Γ ▻ T' ‘’ a)} (W T ‘’₁ a)
  SW₁⁻¹ {a = a} x = S₁W₁ (W₁S₁W⁻¹ (w₁ x) ‘’ᵗ₁ a)

  S₁W⁻¹ = SW₁⁻¹

  _‘∘’_ : ∀ {Γ A B C}
      → Term {Γ} (A ‘→'’ B)
      → Term {Γ} (B ‘→'’ C)
      → Term {Γ} (A ‘→'’ C)
  g ‘∘’ f = ‘λ’ (w→ f ‘'’ₐ (w→ g ‘'’ₐ ‘VAR₀’))


  WSSW₁' : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Type (Γ ▻ A)}
        → Term {Γ ▻ T'} (W (T ‘’ (SW (a ‘’ᵗ b))))
        → Term {Γ ▻ T'} (W (W₁ T ‘’ a ‘’ b))
  WSSW₁' = WSSW₁⁻¹

  SSW₁⁻¹-arr : ∀ {Γ B A}
           {b : Term {Γ} B}
           {a : Term {Γ ▻ B} (W A)}
           {T : Type (Γ ▻ A)}
           {X} →
      Term {Γ} (T ‘’ (SW (a ‘’ᵗ b)) ‘→'’ X)
      → Term {Γ} (W₁ T ‘’ a ‘’ b ‘→'’ X)
  SSW₁⁻¹-arr x = ‘λ’ (w→ x ‘'’ₐ WSSW₁ ‘VAR₀’)

  SSW₁'→ = SSW₁⁻¹-arr

  SSW₁-arr⁻¹ : ∀ {Γ B A}
           {b : Term {Γ} B}
           {a : Term {Γ ▻ B} (W A)}
           {T : Type (Γ ▻ A)}
           {X} →
      Term {Γ} (X ‘→'’ T ‘’ (SW (a ‘’ᵗ b)))
      → Term {Γ} (X ‘→'’ W₁ T ‘’ a ‘’ b)
  SSW₁-arr⁻¹ x = ‘λ’ (WSSW₁' (un‘λ’ x))

  SSW₁'← = SSW₁-arr⁻¹


  SSW₁ : ∀ {Γ B A}
           {b : Term {Γ} B}
           {a : Term {Γ ▻ B} (W A)}
           {T : Type (Γ ▻ A)} →
      Term {Γ} (W₁ T ‘’ a ‘’ b)
      → Term {Γ} (T ‘’ (SW (a ‘’ᵗ b)))
  SSW₁ x = (SW (WSSW₁ (w x) ‘’ᵗ x))

  S₁₀W₂W : ∀ {Γ T' A B T} {a : Term {Γ ▻ T'} (W A)} {b : Term {Γ ▻ T'} (W₁ B ‘’ a)}
        → Term {Γ ▻ T'} (W₂ (W T) ‘’₁ a ‘’ b)
        → Term {Γ ▻ T'} (W₁ T ‘’ a)
  S₁₀W₂W = S₁₀W₂₀
\end{code}

\begin{code}
 module well-typed-syntax-context-helpers where
  open well-typed-syntax
  open well-typed-syntax-helpers

  □_ : Type ε → Set
  □_ T = Term {ε} T
\end{code}

\begin{code}
 module well-typed-quoted-syntax-defs where
  open well-typed-syntax
  open well-typed-syntax-helpers
  open well-typed-syntax-context-helpers

  ‘ε’ : Term {ε} ‘Context’
  ‘ε’ = ⌜ ε ⌝ᶜ

  ‘□’ : Type (ε ▻ ‘Type’ ‘’ ‘ε’)
  ‘□’ = ‘Term’ ‘’₁ ‘ε’

\end{code}

\begin{code}
 module well-typed-syntax-eq-dec where
  open well-typed-syntax

  context-pick-if : ∀ {ℓ} {P : Context → Set ℓ}
                          {Γ : Context}
                          (dummy : P (ε ▻ ‘Σ’ ‘Context’ ‘Type’))
                          (val : P Γ) →
                        P (ε ▻ ‘Σ’ ‘Context’ ‘Type’)
  context-pick-if {P = P} {ε ▻ ‘Σ’ ‘Context’ ‘Type’} dummy val = val
  context-pick-if {P = P} {Γ} dummy val = dummy

  context-pick-if-refl : ∀ {ℓ P dummy val} →
                             context-pick-if {ℓ} {P} {ε ▻ ‘Σ’ ‘Context’ ‘Type’} dummy val ≡ val
  context-pick-if-refl {P = P} = refl

\end{code}

\begin{code}
 module well-typed-quoted-syntax where
  open well-typed-syntax
  open well-typed-syntax-helpers public
  open well-typed-quoted-syntax-defs public
  open well-typed-syntax-context-helpers public
  open well-typed-syntax-eq-dec public

  infixr 2 _‘‘∘’’_

  quote-Σ : (Γv : Σ Context Type) → Term {ε} (‘Σ’ ‘Context’ ‘Type’)
  quote-Σ (Γ , v) = _‘,’_ ⌜ Γ ⌝ᶜ ⌜ v ⌝ᵀ

  _‘‘∘’’_ : ∀ {A B C}
      → □ (‘□’ ‘’ (C ‘‘→'’’ B))
      → □ (‘□’ ‘’ (A ‘‘→'’’ C))
      → □ (‘□’ ‘’ (A ‘‘→'’’ B))
  g ‘‘∘’’ f = (‘‘∘-nd’’ ‘'’ₐ f ‘'’ₐ g)

  Conv0 : ∀ {qH0 qX} →
      Term {(ε ▻ ‘□’ ‘’ qH0)}
            (W (‘□’ ‘’ ⌜ ‘□’ ‘’ qH0 ‘→'’ qX ⌝ᵀ))
      → Term {(ε ▻ ‘□’ ‘’ qH0)}
               (W
                  (‘□’ ‘’ (⌜ ‘□’ ‘’ qH0 ⌝ᵀ ‘‘→'’’ ⌜ qX ⌝ᵀ)))
  Conv0 {qH0} {qX} x = w→ ⌜→'⌝ ‘'’ₐ x

\end{code}

\begin{code}
 module well-typed-syntax-pre-interpreter where
  open well-typed-syntax
  open well-typed-syntax-helpers

  max-level : Level
  max-level = lsuc lzero

  module inner
    (context-pick-if' : ∀ ℓ (P : Context → Set ℓ)
                            (Γ : Context)
                            (dummy : P (ε ▻ ‘Σ’ ‘Context’ ‘Type’))
                            (val : P Γ) →
                          P (ε ▻ ‘Σ’ ‘Context’ ‘Type’))
    (context-pick-if-refl' : ∀ ℓ P dummy val →
                              context-pick-if' ℓ P (ε ▻ ‘Σ’ ‘Context’ ‘Type’) dummy val ≡ val)
    where

    context-pick-if : ∀ {ℓ} {P : Context → Set ℓ}
                            {Γ : Context}
                            (dummy : P (ε ▻ ‘Σ’ ‘Context’ ‘Type’))
                            (val : P Γ) →
                          P (ε ▻ ‘Σ’ ‘Context’ ‘Type’)
    context-pick-if {P = P} dummy val = context-pick-if' _ P _ dummy val
    context-pick-if-refl : ∀ {ℓ P dummy val} →
                              context-pick-if {ℓ} {P} {ε ▻ ‘Σ’ ‘Context’ ‘Type’} dummy val ≡ val
    context-pick-if-refl {P = P} = context-pick-if-refl' _ P _ _

    private
      dummy : Type ε
      dummy = ‘Context’

    cast-helper : ∀ {X T A} {x : Term X} → A ≡ T → Term {ε} (T ‘’ x ‘→'’ A ‘’ x)
    cast-helper refl = ‘λ’ ‘VAR₀’

    cast'-proof : ∀ {T} → Term {ε} (context-pick-if {P = Type} (W dummy) T ‘’ _‘,’_ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ
                  ‘→'’ T ‘’ _‘,’_ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ)
    cast'-proof {T} = cast-helper {‘Σ’ ‘Context’ ‘Type’}
                        {context-pick-if {P = Type} {ε ▻ ‘Σ’ ‘Context’ ‘Type’} (W dummy) T}
                        {T} (sym (context-pick-if-refl {P = Type} {dummy = W dummy}))

    cast-proof : ∀ {T} → Term {ε} (T ‘’ _‘,’_ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ
                  ‘→'’ context-pick-if {P = Type} (W dummy) T ‘’ _‘,’_ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ)
    cast-proof {T} = cast-helper {‘Σ’ ‘Context’ ‘Type’} {T}
                        {context-pick-if {P = Type} {ε ▻ ‘Σ’ ‘Context’ ‘Type’} (W dummy) T}
                        (context-pick-if-refl {P = Type} {dummy = W dummy})

    ‘idfun’ : ∀ {T} → Term {ε} (T ‘→'’ T)
    ‘idfun’ = ‘λ’ ‘VAR₀’

    mutual
      ⟦_⟧ᶜ : (Γ : Context) → Set (lsuc max-level)
      ⟦_⟧ᵀ : {Γ : Context} → Type Γ → ⟦_⟧ᶜ Γ → Set max-level

      ⟦_⟧ᶜ ε = ⊤
      ⟦_⟧ᶜ (Γ ▻ T) = Σ (⟦_⟧ᶜ Γ) (λ Γ' → ⟦_⟧ᵀ T Γ')

      ⟦_⟧ᵀ (T₁ ‘’ x) ⟦Γ⟧ = ⟦_⟧ᵀ T₁ (⟦Γ⟧ , ⟦_⟧ᵗ x ⟦Γ⟧)
      ⟦_⟧ᵀ (T₂ ‘’₁ a) (⟦Γ⟧ , A⇓) = ⟦_⟧ᵀ T₂ ((⟦Γ⟧ , ⟦_⟧ᵗ a ⟦Γ⟧) , A⇓)
      ⟦_⟧ᵀ (T₃ ‘’₂ a) ((⟦Γ⟧ , A⇓) , B⇓) = ⟦_⟧ᵀ T₃ (((⟦Γ⟧ , ⟦_⟧ᵗ a ⟦Γ⟧) , A⇓) , B⇓)
      ⟦_⟧ᵀ (T₃ ‘’₃ a) (((⟦Γ⟧ , A⇓) , B⇓) , C⇓) = ⟦_⟧ᵀ T₃ ((((⟦Γ⟧ , ⟦_⟧ᵗ a ⟦Γ⟧) , A⇓) , B⇓) , C⇓)
      ⟦_⟧ᵀ (W T₁) (⟦Γ⟧ , _) = ⟦_⟧ᵀ T₁ ⟦Γ⟧
      ⟦_⟧ᵀ (W₁ T₂) ((⟦Γ⟧ , A⇓) , B⇓) = ⟦_⟧ᵀ T₂ (⟦Γ⟧ , B⇓)
      ⟦_⟧ᵀ (W₂ T₃) (((⟦Γ⟧ , A⇓) , B⇓) , C⇓) = ⟦_⟧ᵀ T₃ ((⟦Γ⟧ , B⇓) , C⇓)
      ⟦_⟧ᵀ (T ‘→’ T₁) ⟦Γ⟧ = (T⇓ : ⟦_⟧ᵀ T ⟦Γ⟧) → ⟦_⟧ᵀ T₁ (⟦Γ⟧ , T⇓)
      ⟦_⟧ᵀ ‘Context’ ⟦Γ⟧ = Lifted Context
      ⟦_⟧ᵀ ‘Type’ (⟦Γ⟧ , T⇓) = Lifted (Type (lower T⇓))
      ⟦_⟧ᵀ ‘Term’ (⟦Γ⟧ , T⇓ , t⇓) = Lifted (Term (lower t⇓))
      ⟦_⟧ᵀ (‘Σ’ T T₁) ⟦Γ⟧ = Σ (⟦_⟧ᵀ T ⟦Γ⟧) (λ T⇓ → ⟦_⟧ᵀ T₁ (⟦Γ⟧ , T⇓))

      ⟦_⟧ᵗ : ∀ {Γ : Context} {T : Type Γ} → Term T → (⟦Γ⟧ : ⟦_⟧ᶜ Γ) → ⟦_⟧ᵀ T ⟦Γ⟧
      ⟦_⟧ᵗ (w t) (⟦Γ⟧ , A⇓) = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (‘λ’ t) ⟦Γ⟧ T⇓ = ⟦_⟧ᵗ t (⟦Γ⟧ , T⇓)
      ⟦_⟧ᵗ (t ‘’ₐ t₁) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧ (⟦_⟧ᵗ t₁ ⟦Γ⟧)
      ⟦_⟧ᵗ ‘VAR₀’ (⟦Γ⟧ , A⇓) = A⇓
      ⟦_⟧ᵗ (⌜ Γ ⌝ᶜ) ⟦Γ⟧ = lift Γ
      ⟦_⟧ᵗ (⌜ T ⌝ᵀ) ⟦Γ⟧ = lift T
      ⟦_⟧ᵗ (⌜ t ⌝ᵗ) ⟦Γ⟧ = lift t
      ⟦_⟧ᵗ ‘⌜_⌝ᵗ’ ⟦Γ⟧ (lift T⇓) = lift ⌜ T⇓ ⌝ᵗ
      ⟦_⟧ᵗ (‘quote-Σ’ {Γ₀} {Γ₁}) ⟦Γ⟧ (lift Γ , lift T) = lift (_‘,’_ {Γ₁} ⌜ Γ ⌝ᶜ ⌜ T ⌝ᵀ)
      ⟦_⟧ᵗ ‘cast’ ⟦Γ⟧ T⇓ = lift (context-pick-if
                                {P = Type}
                                {lower (Σ.fst T⇓)}
                                (W dummy)
                                (lower (Σ.snd T⇓)))
      ⟦_⟧ᵗ (SW t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (WS∀ t) ⟦Γ⟧ T⇓ = ⟦_⟧ᵗ t ⟦Γ⟧ T⇓
      ⟦_⟧ᵗ (SW₁V t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (W∀ t) ⟦Γ⟧ T⇓ = ⟦_⟧ᵗ t ⟦Γ⟧ T⇓
      ⟦_⟧ᵗ (W∀⁻¹ t) ⟦Γ⟧ T⇓ = ⟦_⟧ᵗ t ⟦Γ⟧ T⇓
      ⟦_⟧ᵗ (WW∀ t) ⟦Γ⟧ T⇓ = ⟦_⟧ᵗ t ⟦Γ⟧ T⇓
      ⟦_⟧ᵗ (S₁∀ t) ⟦Γ⟧ T⇓ = ⟦_⟧ᵗ t ⟦Γ⟧ T⇓
      ⟦_⟧ᵗ (S₁₀W⁻¹ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (S₁₀W t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (WWS₁₀W t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (WS₂₁₀W⁻¹ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (S₂₁₀W t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (W₁₀ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (W₁₀⁻¹ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (W₁₀₁₀ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (S₁W₁ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (W₁SW₁⁻¹ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (W₁SW₁ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (WSSW₁ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (WSSW₁⁻¹ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (SW₁₀ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (WS₂₁₀W₁ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (S₁₀∀ t) ⟦Γ⟧ T⇓ = ⟦_⟧ᵗ t ⟦Γ⟧ T⇓
      ⟦_⟧ᵗ (S₂₀₀W₁₀₀ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (S₁₀W₂₀ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (W₀₁₀ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (β-under-S t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ ‘fst'’ ⟦Γ⟧ (x , p) = x
      ⟦_⟧ᵗ ‘snd'’ (⟦Γ⟧ , (x , p)) = p
      ⟦_⟧ᵗ (_‘,’_ x p) ⟦Γ⟧ = ⟦_⟧ᵗ x ⟦Γ⟧ , ⟦_⟧ᵗ p ⟦Γ⟧
      ⟦_⟧ᵗ (f ‘‘’’ x) ⟦Γ⟧ = lift (lower (⟦_⟧ᵗ f ⟦Γ⟧) ‘’ lower (⟦_⟧ᵗ x ⟦Γ⟧))
      ⟦_⟧ᵗ (f w‘‘’’ x) ⟦Γ⟧ = lift (lower (⟦_⟧ᵗ f ⟦Γ⟧) ‘’ lower (⟦_⟧ᵗ x ⟦Γ⟧))
      ⟦_⟧ᵗ (f ‘‘→'’’ x) ⟦Γ⟧ = lift (lower (⟦_⟧ᵗ f ⟦Γ⟧) ‘→'’ lower (⟦_⟧ᵗ x ⟦Γ⟧))
      ⟦_⟧ᵗ (f w‘‘→'’’ x) ⟦Γ⟧ = lift (lower (⟦_⟧ᵗ f ⟦Γ⟧) ‘→'’ lower (⟦_⟧ᵗ x ⟦Γ⟧))
      ⟦_⟧ᵗ (w→ x) ⟦Γ⟧ A⇓ = ⟦_⟧ᵗ x (Σ.fst ⟦Γ⟧) A⇓
      ⟦_⟧ᵗ w‘‘→'’’→‘‘→'’’ ⟦Γ⟧ T⇓ = T⇓
      ⟦_⟧ᵗ ‘‘→'’’→w‘‘→'’’ ⟦Γ⟧ T⇓ = T⇓
      ⟦_⟧ᵗ ‘tApp-nd’ ⟦Γ⟧ f⇓ x⇓ = lift (SW (lower f⇓ ‘’ₐ lower x⇓))
      ⟦_⟧ᵗ ⌜←'⌝ ⟦Γ⟧ T⇓ = T⇓
      ⟦_⟧ᵗ ⌜→'⌝ ⟦Γ⟧ T⇓ = T⇓
      ⟦_⟧ᵗ (‘‘∘-nd’’ {A} {B} {C}) ⟦Γ⟧ g⇓ f⇓ = lift (_‘∘’_ {ε} (lower g⇓) (lower f⇓))
      ⟦_⟧ᵗ (⌜‘’⌝ {B} {A} {b}) ⟦Γ⟧ = lift (‘λ’ {ε} (‘VAR₀’ {ε} {_‘’_ {ε} A b}))
      ⟦_⟧ᵗ (⌜‘’⌝' {B} {A} {b}) ⟦Γ⟧ = lift (‘λ’ {ε} (‘VAR₀’ {ε} {_‘’_ {ε} A b}))
      ⟦_⟧ᵗ (‘cast-refl’ {T}) ⟦Γ⟧ = lift (cast-proof {T})
      ⟦_⟧ᵗ (‘cast-refl'’ {T}) ⟦Γ⟧ = lift (cast'-proof {T})
      ⟦_⟧ᵗ (‘s→→’ {T} {B} {b} {c} {v}) ⟦Γ⟧ = lift (‘idfun’ {_‘’_ {ε} (lower (⟦_⟧ᵗ b tt (⟦_⟧ᵗ v ⟦Γ⟧))) (lower (⟦_⟧ᵗ c tt (⟦_⟧ᵗ v ⟦Γ⟧)))})
      ⟦_⟧ᵗ (‘s←←’ {T} {B} {b} {c} {v}) ⟦Γ⟧ = lift (‘idfun’ {_‘’_ {ε} (lower (⟦_⟧ᵗ b tt (⟦_⟧ᵗ v ⟦Γ⟧))) (lower (⟦_⟧ᵗ c tt (⟦_⟧ᵗ v ⟦Γ⟧)))})
\end{code}

\begin{code}
 module well-typed-syntax-interpreter where
  open well-typed-syntax
  open well-typed-syntax-eq-dec

  max-level : Level
  max-level = well-typed-syntax-pre-interpreter.max-level

  ⟦_⟧ᶜ : (Γ : Context) → Set (lsuc max-level)
  ⟦_⟧ᶜ = well-typed-syntax-pre-interpreter.inner.⟦_⟧ᶜ
             (λ ℓ P Γ' dummy val → context-pick-if {P = P} dummy val)
             (λ ℓ P dummy val → context-pick-if-refl {P = P} {dummy})

  ⟦_⟧ᵀ : {Γ : Context} → Type Γ → ⟦_⟧ᶜ Γ → Set max-level
  ⟦_⟧ᵀ = well-typed-syntax-pre-interpreter.inner.⟦_⟧ᵀ
         (λ ℓ P Γ' dummy val → context-pick-if {P = P} dummy val)
         (λ ℓ P dummy val → context-pick-if-refl {P = P} {dummy})

  ⟦_⟧ᵗ : ∀ {Γ : Context} {T : Type Γ} → Term T → (⟦Γ⟧ : ⟦_⟧ᶜ Γ) → ⟦_⟧ᵀ T ⟦Γ⟧
  ⟦_⟧ᵗ = well-typed-syntax-pre-interpreter.inner.⟦_⟧ᵗ
          (λ ℓ P Γ' dummy val → context-pick-if {P = P} dummy val)
          (λ ℓ P dummy val → context-pick-if-refl {P = P} {dummy})

\end{code}

\begin{code}
 module well-typed-syntax-interpreter-full where
  open well-typed-syntax
  open well-typed-syntax-interpreter

  ⟦ε⟧ᶜ : ⟦ ε ⟧ᶜ
  ⟦ε⟧ᶜ = tt

  ⟦_⟧ᵀε : Type ε → Set max-level
  ⟦ T ⟧ᵀε = ⟦ T ⟧ᵀ ⟦ε⟧ᶜ

  ⟦_⟧ᵗε : {T : Type ε} → Term T → ⟦_⟧ᵀε T
  ⟦ t ⟧ᵗε = ⟦ t ⟧ᵗ ⟦ε⟧ᶜ

  ⟦_⟧ᵀε▻ : ∀ {A} → Type (ε ▻ A) → ⟦ A ⟧ᵀε → Set max-level
  ⟦ T ⟧ᵀε▻ ⟦A⟧ = ⟦ T ⟧ᵀ (⟦ε⟧ᶜ , ⟦A⟧)

  ⟦_⟧ᵗε▻ : ∀ {A} → {T : Type (ε ▻ A)} → Term T → (x : ⟦ A ⟧ᵀε) → ⟦ T ⟧ᵀε▻ x
  ⟦ t ⟧ᵗε▻ x = ⟦ t ⟧ᵗ (⟦ε⟧ᶜ , x)

\end{code}

\begin{code}
 module lӧb where
  open well-typed-syntax
  open well-typed-quoted-syntax
  open well-typed-syntax-interpreter-full

  module inner (‘X’ : Type ε) (‘f’ : Term {ε ▻ (‘□’ ‘’ ⌜ ‘X’ ⌝ᵀ)} (W ‘X’)) where
    X : Set _
    X = ⟦ ‘X’ ⟧ᵀε

    f'' : (x : ⟦_⟧ᵀε (‘□’ ‘’ ⌜ ‘X’ ⌝ᵀ)) → ⟦_⟧ᵀε▻ {‘□’ ‘’ ⌜ ‘X’ ⌝ᵀ} (W ‘X’) x
    f'' = ⟦ ‘f’ ⟧ᵗε▻

    dummy : Type ε
    dummy = ‘Context’

    cast : (Γv : Σ Context Type) → Type (ε ▻ ‘Σ’ ‘Context’ ‘Type’)
    cast (Γ , v) = context-pick-if {P = Type} {Γ} (W dummy) v

    Hf : (h : Σ Context Type) → Type ε
    Hf h = (cast h ‘’ quote-Σ h ‘→'’ ‘X’)

    qh : Term {(ε ▻ ‘Σ’ ‘Context’ ‘Type’)} (W (‘Type’ ‘’ ‘ε’))
    qh = f' w‘‘’’ x
      where
        f' : Term (W (‘Type’ ‘’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ))
        f' = w→ ‘cast’ ‘'’ₐ ‘VAR₀’

        x : Term (W (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’ ⌜ ‘Σ’ ‘Context’ ‘Type’ ⌝ᵀ))
        x = (w→ ‘quote-Σ’ ‘'’ₐ ‘VAR₀’)

    h₂ : Type (ε ▻ ‘Σ’ ‘Context’ ‘Type’)
    h₂ = (W₁ ‘□’ ‘’ (qh w‘‘→'’’ w ⌜ ‘X’ ⌝ᵀ))

    h : Σ Context Type
    h = ((ε ▻ ‘Σ’ ‘Context’ ‘Type’) , h₂)

    H0 : Type ε
    H0 = Hf h

    H : Set
    H = Term {ε} H0

    ‘H0’ : □ (‘Type’ ‘’ ⌜ ε ⌝ᶜ)
    ‘H0’ = ⌜ H0 ⌝ᵀ

    ‘H’ : Type ε
    ‘H’ = ‘□’ ‘’ ‘H0’

    H0' : Type ε
    H0' = ‘H’ ‘→'’ ‘X’

    H' : Set
    H' = Term {ε} H0'

    ‘H0'’ : □ (‘Type’ ‘’ ⌜ ε ⌝ᶜ)
    ‘H0'’ = ⌜ H0' ⌝ᵀ

    ‘H'’ : Type ε
    ‘H'’ = ‘□’ ‘’ ‘H0'’

    toH-helper-helper : ∀ {k} → h₂ ≡ k
      → □ (h₂ ‘’ quote-Σ h ‘→'’ ‘□’ ‘’ ⌜ h₂ ‘’ quote-Σ h ‘→'’ ‘X’ ⌝ᵀ)
      → □ (k ‘’ quote-Σ h ‘→'’ ‘□’ ‘’ ⌜ k ‘’ quote-Σ h ‘→'’ ‘X’ ⌝ᵀ)
    toH-helper-helper p x = transport (λ k → □ (k ‘’ quote-Σ h ‘→'’ ‘□’ ‘’ ⌜ k ‘’ quote-Σ h ‘→'’ ‘X’ ⌝ᵀ)) p x

    toH-helper : □ (cast h ‘’ quote-Σ h ‘→'’ ‘H’)
    toH-helper = toH-helper-helper
      {k = context-pick-if {P = Type} {ε ▻ ‘Σ’ ‘Context’ ‘Type’} (W dummy) h₂}
      (sym (context-pick-if-refl {P = Type} {W dummy} {h₂}))
      (SSW₁'→ ((‘‘→'’’→w‘‘→'’’ ‘∘’ ‘‘∘-nd’’ ‘'’ₐ (‘s←←’ ‘‘∘’’ ‘cast-refl’ ‘‘∘’’ ⌜→'⌝ ‘'’ₐ ⌜ ‘λ’ ‘VAR₀’ ⌝ᵗ)) ‘∘’ ⌜←'⌝))

    ‘toH’ : □ (‘H'’ ‘→'’ ‘H’)
    ‘toH’ = ⌜→'⌝ ‘∘’ ‘‘∘-nd’’ ‘'’ₐ (⌜→'⌝ ‘'’ₐ ⌜ toH-helper ⌝ᵗ) ‘∘’ ⌜←'⌝

    toH : H' → H
    toH h' = toH-helper ‘∘’ h'

    fromH-helper-helper : ∀ {k} → h₂ ≡ k
      → □ (‘□’ ‘’ ⌜ h₂ ‘’ quote-Σ h ‘→'’ ‘X’ ⌝ᵀ ‘→'’ h₂ ‘’ quote-Σ h)
      → □ (‘□’ ‘’ ⌜ k ‘’ quote-Σ h ‘→'’ ‘X’ ⌝ᵀ ‘→'’ k ‘’ quote-Σ h)
    fromH-helper-helper p x = transport (λ k → □ (‘□’ ‘’ ⌜ k ‘’ quote-Σ h ‘→'’ ‘X’ ⌝ᵀ ‘→'’ k ‘’ quote-Σ h)) p x

    fromH-helper : □ (‘H’ ‘→'’ cast h ‘’ quote-Σ h)
    fromH-helper = fromH-helper-helper
      {k = context-pick-if {P = Type} {ε ▻ ‘Σ’ ‘Context’ ‘Type’} (W dummy) h₂}
      (sym (context-pick-if-refl {P = Type} {W dummy} {h₂}))
      (SSW₁'← (⌜→'⌝ ‘∘’ ‘‘∘-nd’’ ‘'’ₐ (⌜→'⌝ ‘'’ₐ ⌜ ‘λ’ ‘VAR₀’ ⌝ᵗ ‘‘∘’’ ‘cast-refl'’ ‘‘∘’’ ‘s→→’) ‘∘’ w‘‘→'’’→‘‘→'’’))

    ‘fromH’ : □ (‘H’ ‘→'’ ‘H'’)
    ‘fromH’ = ⌜→'⌝ ‘∘’ ‘‘∘-nd’’ ‘'’ₐ (⌜→'⌝ ‘'’ₐ ⌜ fromH-helper ⌝ᵗ) ‘∘’ ⌜←'⌝

    fromH : H → H'
    fromH h' = fromH-helper ‘∘’ h'

    lob : □ ‘X’
    lob = fromH h' ‘'’ₐ ⌜ h' ⌝ᵗ
      where
        f' : Term {ε ▻ ‘□’ ‘’ ‘H0’} (W (‘□’ ‘’ (⌜ ‘□’ ‘’ ‘H0’ ⌝ᵀ ‘‘→'’’ ⌜ ‘X’ ⌝ᵀ)))
        f' = Conv0 {‘H0’} {‘X’} (SW₁₀ (w∀ ‘fromH’ ‘’ₐ ‘VAR₀’))

        x : Term {ε ▻ ‘□’ ‘’ ‘H0’} (W (‘□’ ‘’ ⌜ ‘H’ ⌝ᵀ))
        x = w→ ‘⌜_⌝ᵗ’ ‘'’ₐ ‘VAR₀’

        h' : H
        h' = toH (‘λ’ (w→ (‘λ’ ‘f’) ‘'’ₐ (w→→ ‘tApp-nd’ ‘'’ₐ f' ‘'’ₐ x)))

  lob : {‘X’ : Type ε} → □ ((‘□’ ‘’ ⌜ ‘X’ ⌝ᵀ) ‘→'’ ‘X’) → □ ‘X’
  lob {‘X’} ‘f’ = inner.lob ‘X’ (un‘λ’ ‘f’)

\end{code}
