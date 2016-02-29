\section{Encoding with Add-Quote Function}

\AgdaHide{
  \begin{code}
module lob-appendix where
open import lob
  \end{code}
}


\begin{code}
module lob-by-repr where
 module well-typed-syntax where

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
    ‘quote-term’ : ∀ {Γ Γ'} {A : Type Γ'} → Term {Γ} (‘Term’ ‘’₁ ⌜ Γ' ⌝ᶜ ‘’ ⌜ A ⌝ᵀ ‘→’ W (‘Term’ ‘’₁ ⌜ Γ ⌝ᶜ ‘’ ⌜ ‘Term’ ‘’₁ ⌜ Γ' ⌝ᶜ ‘’ ⌜ A ⌝ᵀ ⌝ᵀ))
    ‘quote-sigma’ : ∀ {Γ Γ'} → Term {Γ} (‘Σ’ ‘Context’ ‘Type’ ‘→’ W (‘Term’ ‘’₁ ⌜ Γ' ⌝ᶜ ‘’ ⌜ ‘Σ’ ‘Context’ ‘Type’ ⌝ᵀ))
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
    W₁₀-inv : ∀ {Γ A B C} → Term {Γ ▻ A ▻ W B} (W (W C)) → Term {Γ ▻ A ▻ W B} (W₁ (W C))
    W₁₀₁₀ : ∀ {Γ A B C T} → Term {Γ ▻ A ▻ B ▻ W (W C)} (W₁ (W₁ (W T))) → Term {Γ ▻ A ▻ B ▻ W (W C)} (W₁ (W (W T)))
    S₁W₁ : ∀ {Γ A B C} {a : Term {Γ} A} → Term {Γ ▻ W B ‘’ a} (W₁ C ‘’₁ a) → Term {Γ ▻ B} C
    weakenType1-substType-weakenType1-inv : ∀ {Γ A T'' T' T} {a : Term {Γ} A}
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W₁ (W (T ‘’ a)))
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W₁ (W T ‘’₁ a))
    weakenType1-substType-weakenType1 : ∀ {Γ A T'' T' T} {a : Term {Γ} A}
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W₁ (W T ‘’₁ a))
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W₁ (W (T ‘’ a)))
    weakenType-substType-substType-weakenType1 : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Type (Γ ▻ A)}
      → Term {Γ ▻ T'} (W (W₁ T ‘’ a ‘’ b))
      → Term {Γ ▻ T'} (W (T ‘’ (SW ((‘λ’ a) ‘’ₐ b))))
    weakenType-substType-substType-weakenType1-inv : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Type (Γ ▻ A)}
      → Term {Γ ▻ T'} (W (T ‘’ (SW ((‘λ’ a) ‘’ₐ b))))
      → Term {Γ ▻ T'} (W (W₁ T ‘’ a ‘’ b))
    substType-W₁₀ : ∀ {Γ T} {A : Type Γ} {B : Type Γ}
      → {a : Term {Γ ▻ T} (W {Γ} {T} B)}
      → Term {Γ ▻ T} (W₁ (W A) ‘’ a)
      → Term {Γ ▻ T} (W A)
    WS₂₁₀W₁ : ∀ {Γ A B C T T'} {a : Term {Γ} A} {b : Term (B ‘’ a)} {c : Term (C ‘’ a)}
      → Term {(Γ ▻ T')} (W (W₁ T ‘’₂ a ‘’₁ b ‘’ S₁₀W⁻¹ c))
      → Term {(Γ ▻ T')} (W (T ‘’₁ a ‘’ c))
    substType1-substType-tProd : ∀ {Γ T T' A B a b} → Term ((_‘→’_ {Γ ▻ T ▻ T'} A B) ‘’₁ a ‘’ b) → Term (_‘→’_ {Γ} (A ‘’₁ a ‘’ b) (B ‘’₂ a ‘’₁ b))
    substType2-substType-substType-W₁₀-weakenType : ∀ {Γ A} {T : Type (Γ ▻ A)} {T' C B} {a : Term {Γ} A} {b : Term {(Γ ▻ C ‘’ a)} (B ‘’₁ a)}
         {c : Term {(Γ ▻ T')} (W (C ‘’ a))}
         → Term {(Γ ▻ T')} (W₁ (W (W T) ‘’₂ a ‘’ b) ‘’ c)
         → Term {(Γ ▻ T')} (W (T ‘’ a))
    S₁₀W2-weakenType : ∀ {Γ T' A B T} {a : Term {Γ ▻ T'} (W A)} {b : Term {Γ ▻ T'} (W₁ B ‘’ a)}
      → Term {Γ ▻ T'} (W₂ (W T) ‘’₁ a ‘’ b)
      → Term {Γ ▻ T'} (W₁ T ‘’ a)
    weakenType-W₁₀ : ∀ {Γ A B C D} → Term {Γ ▻ A ▻ W B ▻ W₁ C} (W (W₁ (W D))) → Term {Γ ▻ A ▻ W B ▻ W₁ C} (W (W (W D)))
    beta-under-subst : ∀ {Γ A B B'} {g : Term {Γ} (A ‘→’ W B)} {x : Term {Γ} A}
      → Term (B' ‘’ SW (‘λ’ (SW (‘λ’ (W₁₀ (SW₁V (W∀ (w (W∀ (w g))) ‘’ₐ ‘VAR₀’))) ‘’ₐ ‘VAR₀’)) ‘’ₐ x))
      → Term (B' ‘’ SW (g ‘’ₐ x))
    ‘proj₁'’ : ∀ {Γ} {T : Type Γ} {P : Type (Γ ▻ T)} → Term (‘Σ’ T P ‘→’ W T)
    ‘proj₂'’ : ∀ {Γ} {T : Type Γ} {P : Type (Γ ▻ T)} → Term {Γ ▻ ‘Σ’ T P} (W₁ P ‘’ SW (‘λ’ (W₁₀ (SW₁V (W∀ (w (W∀ (w ‘proj₁'’))) ‘’ₐ ‘VAR₀’))) ‘’ₐ ‘VAR₀’))
    ‘existT’ : ∀ {Γ T P} (x : Term {Γ} T) (p : Term (P ‘’ x)) → Term (‘Σ’ T P)
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
    ‘‘fcomp-nd’’ : ∀ {A B C} →
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
            ((⌜ T ‘’ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ ⌝ᵀ)
               ‘‘→'’’
               (SW (‘cast’ ‘’ₐ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ)
                 ‘‘’’ SW (‘quote-sigma’ ‘’ₐ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ))))
    ‘cast-refl'’ : ∀ {T : Type (ε ▻ ‘Σ’ ‘Context’ ‘Type’)} →
        Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’
            ((SW (‘cast’ ‘’ₐ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ)
                 ‘‘’’ SW (‘quote-sigma’ ‘’ₐ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ))
               ‘‘→'’’
               (⌜ T ‘’ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ ⌝ᵀ)))
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
  infixl 3 _‘t’_
  infixl 3 _‘t’₁_
  infixl 3 _‘t’₂_
  infixr 2 _‘∘’_

  _‘→'’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
  _‘→'’_ {Γ} A B = _‘→’_ {Γ} A (W {Γ} {A} B)

  _‘'’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→'’ B) → Term A → Term B
  _‘'’ₐ_ {Γ} {A} {B} f x = SW (_‘’ₐ_ {Γ} {A} {W B} f x)

  _‘t’_ : ∀ {Γ A} {B : Type (Γ ▻ A)} → (b : Term {Γ ▻ A} B) → (a : Term {Γ} A) → Term {Γ} (B ‘’ a)
  b ‘t’ a = ‘λ’ b ‘’ₐ a

  substType-tProd : ∀ {Γ T A B} {a : Term {Γ} T} →
                           Term {Γ} ((A ‘→’ B) ‘’ a)
                           → Term {Γ} (_‘→’_ {Γ} (A ‘’ a) (B ‘’₁ a))
  substType-tProd {Γ} {T} {A} {B} {a} x = SW ((WS∀ (w x)) ‘t’ a)

  S∀ = substType-tProd

  ‘λ'∙’ : ∀ {Γ A B} → Term {Γ ▻ A} (W B) -> Term (A ‘→'’ B)
  ‘λ'∙’ f = ‘λ’ f

  un‘λ’ : ∀ {Γ A B} → Term (A ‘→’ B) → Term {Γ ▻ A} B
  un‘λ’ f = SW₁V (W∀ (w f) ‘’ₐ ‘VAR₀’)

  weakenProd : ∀ {Γ A B C} →
                            Term {Γ} (A ‘→’ B)
                            → Term {Γ ▻ C} (W A ‘→’ W₁ B)
  weakenProd {Γ} {A} {B} {C} x = W∀ (w x)
  w∀ = weakenProd

  w1 : ∀ {Γ A B C} → Term {Γ ▻ B} C → Term {Γ ▻ A ▻ W {Γ} {A} B} (W₁ {Γ} {A} {B = B} C)
  w1 x = un‘λ’ (W∀ (w (‘λ’ x)))

  _‘t’₁_ : ∀ {Γ A B C} → (c : Term {Γ ▻ A ▻ B} C) → (a : Term {Γ} A) → Term {Γ ▻ B ‘’ a} (C ‘’₁ a)
  f ‘t’₁ x = un‘λ’ (S∀ (‘λ’ (‘λ’ f) ‘’ₐ x))
  _‘t’₂_ : ∀ {Γ A B C D} → (c : Term {Γ ▻ A ▻ B ▻ C} D) → (a : Term {Γ} A) → Term {Γ ▻ B ‘’ a ▻ C ‘’₁ a} (D ‘’₂ a)
  f ‘t’₂ x = un‘λ’ (S₁∀ (un‘λ’ (S∀ (‘λ’ (‘λ’ (‘λ’ f)) ‘’ₐ x))))

  S₁₀W' : ∀ {Γ C T A} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ} (A ‘’ a) → Term {Γ} (W A ‘’₁ a ‘’ b)
  S₁₀W' = S₁₀W⁻¹

  S₁₀W-weakenType : ∀ {Γ T A} {B : Type (Γ ▻ A)}
      → {a : Term {Γ} A}
      → {b : Term {Γ} (B ‘’ a)}
      → Term {Γ} (W (W T) ‘’₁ a ‘’ b)
      → Term {Γ} T
  S₁₀W-weakenType x = SW (S₁₀W x)

  S₁₀WW = S₁₀W-weakenType


  S₂₁₀W-weakenType : ∀ {Γ A B C T}
           {a : Term {Γ} A}
           {b : Term {Γ} (B ‘’ a)}
           {c : Term {Γ} (C ‘’₁ a ‘’ b)} →
      Term {Γ} (W (W T) ‘’₂ a ‘’₁ b ‘’ c)
      → Term {Γ} (T ‘’ a)
  S₂₁₀W-weakenType x = S₁₀W (S₂₁₀W x)

  S₂₁₀WW = S₂₁₀W-weakenType

  W₁₀₁W : ∀ {Γ A B C T} → Term {Γ ▻ A ▻ B ▻ W (W C)} (W₁ (W₁ (W T))) → Term {Γ ▻ A ▻ B ▻ W (W C)} (W₁ (W (W T)))
  W₁₀₁W = W₁₀₁₀

  W∀-nd : ∀ {Γ A B C} →
                            Term {Γ ▻ C} (W (A ‘→'’ B))
                            → Term {Γ ▻ C} (W A ‘→'’ W B)
  W∀-nd x = ‘λ'∙’ (W₁₀ (SW₁V (W∀ (w (W∀ x)) ‘’ₐ ‘VAR₀’)))

  weakenProd-nd : ∀ {Γ A B C} →
                               Term (A ‘→'’ B)
                               → Term {Γ ▻ C} (W A ‘→'’ W B)
  weakenProd-nd {Γ} {A} {B} {C} x = W∀-nd (w x)




  W∀-nd-tProd-nd : ∀ {Γ A B C D} →
      Term {Γ ▻ D} (W (A ‘→'’ B ‘→'’ C))
      → Term {Γ ▻ D} (W A ‘→'’ W B ‘→'’ W C)
  W∀-nd-tProd-nd x = ‘λ’ (W∀⁻¹ (‘λ’ (W₁₀₁W (SW₁V (w∀ (W∀ (WW∀ (w→ (W∀-nd x) ‘'’ₐ ‘VAR₀’))) ‘’ₐ ‘VAR₀’)))))

  weakenProd-nd-Prod-nd : ∀ {Γ A B C D} →
      Term (A ‘→'’ B ‘→'’ C)
      → Term {Γ ▻ D} (W A ‘→'’ W B ‘→'’ W C)
  weakenProd-nd-Prod-nd {Γ} {A} {B} {C} {D} x = W∀-nd-tProd-nd (w x)
  w→→ = weakenProd-nd-Prod-nd

  W₁S₁W' : ∀ {Γ A T'' T' T} {a : Term {Γ} A}
        → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W₁ (W (T ‘’ a)))
        → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W₁ (W T ‘’₁ a))
  W₁S₁W' = weakenType1-substType-weakenType1-inv


  substType-weakenType1-inv : ∀ {Γ A T' T}
           {a : Term {Γ} A} →
      Term {(Γ ▻ T' ‘’ a)} (W (T ‘’ a))
      → Term {(Γ ▻ T' ‘’ a)} (W T ‘’₁ a)
  substType-weakenType1-inv {a = a} x = S₁W₁ (W₁S₁W' (w1 x) ‘t’₁ a)

  S₁W' = substType-weakenType1-inv

  _‘∘’_ : ∀ {Γ A B C}
      → Term {Γ} (A ‘→'’ B)
      → Term {Γ} (B ‘→'’ C)
      → Term {Γ} (A ‘→'’ C)
  g ‘∘’ f = ‘λ’ (w→ f ‘'’ₐ (w→ g ‘'’ₐ ‘VAR₀’))


  WS₀₀W₁ : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Type (Γ ▻ A)}
        → Term {Γ ▻ T'} (W (W₁ T ‘’ a ‘’ b))
        → Term {Γ ▻ T'} (W (T ‘’ (SW (a ‘t’ b))))
  WS₀₀W₁ = weakenType-substType-substType-weakenType1

  WS₀₀W₁' : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Type (Γ ▻ A)}
        → Term {Γ ▻ T'} (W (T ‘’ (SW (a ‘t’ b))))
        → Term {Γ ▻ T'} (W (W₁ T ‘’ a ‘’ b))
  WS₀₀W₁' = weakenType-substType-substType-weakenType1-inv

  substType-substType-weakenType1-inv-arr : ∀ {Γ B A}
           {b : Term {Γ} B}
           {a : Term {Γ ▻ B} (W A)}
           {T : Type (Γ ▻ A)}
           {X} →
      Term {Γ} (T ‘’ (SW (a ‘t’ b)) ‘→'’ X)
      → Term {Γ} (W₁ T ‘’ a ‘’ b ‘→'’ X)
  substType-substType-weakenType1-inv-arr x = ‘λ’ (w→ x ‘'’ₐ WS₀₀W₁ ‘VAR₀’)

  S₀₀W₁'→ = substType-substType-weakenType1-inv-arr

  substType-substType-weakenType1-arr-inv : ∀ {Γ B A}
           {b : Term {Γ} B}
           {a : Term {Γ ▻ B} (W A)}
           {T : Type (Γ ▻ A)}
           {X} →
      Term {Γ} (X ‘→'’ T ‘’ (SW (a ‘t’ b)))
      → Term {Γ} (X ‘→'’ W₁ T ‘’ a ‘’ b)
  substType-substType-weakenType1-arr-inv x = ‘λ’ (WS₀₀W₁' (un‘λ’ x))

  S₀₀W₁'← = substType-substType-weakenType1-arr-inv


  substType-substType-weakenType1 : ∀ {Γ B A}
           {b : Term {Γ} B}
           {a : Term {Γ ▻ B} (W A)}
           {T : Type (Γ ▻ A)} →
      Term {Γ} (W₁ T ‘’ a ‘’ b)
      → Term {Γ} (T ‘’ (SW (a ‘t’ b)))
  substType-substType-weakenType1 x = (SW (WS₀₀W₁ (w x) ‘t’ x))
  S₀₀W₁ = substType-substType-weakenType1

  SW₁₀ : ∀ {Γ T} {A : Type Γ} {B : Type Γ}
        → {a : Term {Γ ▻ T} (W {Γ} {T} B)}
        → Term {Γ ▻ T} (W₁ (W A) ‘’ a)
        → Term {Γ ▻ T} (W A)
  SW₁₀ = substType-W₁₀


  S₂₀₀W₁₀W : ∀ {Γ A} {T : Type (Γ ▻ A)} {T' C B} {a : Term {Γ} A} {b : Term {(Γ ▻ C ‘’ a)} (B ‘’₁ a)}
           {c : Term {(Γ ▻ T')} (W (C ‘’ a))}
           → Term {(Γ ▻ T')} (W₁ (W (W T) ‘’₂ a ‘’ b) ‘’ c)
           → Term {(Γ ▻ T')} (W (T ‘’ a))
  S₂₀₀W₁₀W = substType2-substType-substType-W₁₀-weakenType


  S₁₀W₂W : ∀ {Γ T' A B T} {a : Term {Γ ▻ T'} (W A)} {b : Term {Γ ▻ T'} (W₁ B ‘’ a)}
        → Term {Γ ▻ T'} (W₂ (W T) ‘’₁ a ‘’ b)
        → Term {Γ ▻ T'} (W₁ T ‘’ a)
  S₁₀W₂W = S₁₀W2-weakenType
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

  quote-sigma : (Γv : Σ Context Type) → Term {ε} (‘Σ’ ‘Context’ ‘Type’)
  quote-sigma (Γ , v) = ‘existT’ ⌜ Γ ⌝ᶜ ⌜ v ⌝ᵀ

  _‘‘∘’’_ : ∀ {A B C}
      → □ (‘□’ ‘’ (C ‘‘→'’’ B))
      → □ (‘□’ ‘’ (A ‘‘→'’’ C))
      → □ (‘□’ ‘’ (A ‘‘→'’’ B))
  g ‘‘∘’’ f = (‘‘fcomp-nd’’ ‘'’ₐ f ‘'’ₐ g)

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

    cast'-proof : ∀ {T} → Term {ε} (context-pick-if {P = Type} (W dummy) T ‘’ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ
                  ‘→'’ T ‘’ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ)
    cast'-proof {T} = cast-helper {‘Σ’ ‘Context’ ‘Type’}
                        {context-pick-if {P = Type} {ε ▻ ‘Σ’ ‘Context’ ‘Type’} (W dummy) T}
                        {T} (sym (context-pick-if-refl {P = Type} {dummy = W dummy}))

    cast-proof : ∀ {T} → Term {ε} (T ‘’ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ
                  ‘→'’ context-pick-if {P = Type} (W dummy) T ‘’ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ ⌜ T ⌝ᵀ)
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
      ⟦_⟧ᵗ ‘quote-term’ ⟦Γ⟧ (lift T⇓) = lift ⌜ T⇓ ⌝ᵗ
      ⟦_⟧ᵗ (‘quote-sigma’ {Γ₀} {Γ₁}) ⟦Γ⟧ (lift Γ , lift T) = lift (‘existT’ {Γ₁} ⌜ Γ ⌝ᶜ ⌜ T ⌝ᵀ)
      ⟦_⟧ᵗ ‘cast’ ⟦Γ⟧ T⇓ = lift (context-pick-if
                                {P = Type}
                                {lower (Σ.proj₁ T⇓)}
                                (W dummy)
                                (lower (Σ.proj₂ T⇓)))
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
      ⟦_⟧ᵗ (W₁₀-inv t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (W₁₀₁₀ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (S₁W₁ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (weakenType1-substType-weakenType1-inv t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (weakenType1-substType-weakenType1 t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (weakenType-substType-substType-weakenType1 t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (weakenType-substType-substType-weakenType1-inv t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (substType-W₁₀ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (WS₂₁₀W₁ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (substType1-substType-tProd t) ⟦Γ⟧ T⇓ = ⟦_⟧ᵗ t ⟦Γ⟧ T⇓
      ⟦_⟧ᵗ (substType2-substType-substType-W₁₀-weakenType t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (S₁₀W2-weakenType t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (weakenType-W₁₀ t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ (beta-under-subst t) ⟦Γ⟧ = ⟦_⟧ᵗ t ⟦Γ⟧
      ⟦_⟧ᵗ ‘proj₁'’ ⟦Γ⟧ (x , p) = x
      ⟦_⟧ᵗ ‘proj₂'’ (⟦Γ⟧ , (x , p)) = p
      ⟦_⟧ᵗ (‘existT’ x p) ⟦Γ⟧ = ⟦_⟧ᵗ x ⟦Γ⟧ , ⟦_⟧ᵗ p ⟦Γ⟧
      ⟦_⟧ᵗ (f ‘‘’’ x) ⟦Γ⟧ = lift (lower (⟦_⟧ᵗ f ⟦Γ⟧) ‘’ lower (⟦_⟧ᵗ x ⟦Γ⟧))
      ⟦_⟧ᵗ (f w‘‘’’ x) ⟦Γ⟧ = lift (lower (⟦_⟧ᵗ f ⟦Γ⟧) ‘’ lower (⟦_⟧ᵗ x ⟦Γ⟧))
      ⟦_⟧ᵗ (f ‘‘→'’’ x) ⟦Γ⟧ = lift (lower (⟦_⟧ᵗ f ⟦Γ⟧) ‘→'’ lower (⟦_⟧ᵗ x ⟦Γ⟧))
      ⟦_⟧ᵗ (f w‘‘→'’’ x) ⟦Γ⟧ = lift (lower (⟦_⟧ᵗ f ⟦Γ⟧) ‘→'’ lower (⟦_⟧ᵗ x ⟦Γ⟧))
      ⟦_⟧ᵗ (w→ x) ⟦Γ⟧ A⇓ = ⟦_⟧ᵗ x (Σ.proj₁ ⟦Γ⟧) A⇓
      ⟦_⟧ᵗ w‘‘→'’’→‘‘→'’’ ⟦Γ⟧ T⇓ = T⇓
      ⟦_⟧ᵗ ‘‘→'’’→w‘‘→'’’ ⟦Γ⟧ T⇓ = T⇓
      ⟦_⟧ᵗ ‘tApp-nd’ ⟦Γ⟧ f⇓ x⇓ = lift (SW (lower f⇓ ‘’ₐ lower x⇓))
      ⟦_⟧ᵗ ⌜←'⌝ ⟦Γ⟧ T⇓ = T⇓
      ⟦_⟧ᵗ ⌜→'⌝ ⟦Γ⟧ T⇓ = T⇓
      ⟦_⟧ᵗ (‘‘fcomp-nd’’ {A} {B} {C}) ⟦Γ⟧ g⇓ f⇓ = lift (_‘∘’_ {ε} (lower g⇓) (lower f⇓))
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

  Contextε⇓ : ⟦_⟧ᶜ ε
  Contextε⇓ = tt

  Typeε⇓ : Type ε → Set max-level
  Typeε⇓ T = ⟦_⟧ᵀ T Contextε⇓

  Termε⇓ : {T : Type ε} → Term T → Typeε⇓ T
  Termε⇓ t = ⟦_⟧ᵗ t Contextε⇓

  Typeε▻⇓ : ∀ {A} → Type (ε ▻ A) → Typeε⇓ A → Set max-level
  Typeε▻⇓ T A⇓ = ⟦_⟧ᵀ T (Contextε⇓ , A⇓)

  Termε▻⇓ : ∀ {A} → {T : Type (ε ▻ A)} → Term T → (x : Typeε⇓ A) → Typeε▻⇓ T x
  Termε▻⇓ t x = ⟦_⟧ᵗ t (Contextε⇓ , x)

\end{code}

\begin{code}
 module lӧb where
  open well-typed-syntax
  open well-typed-quoted-syntax
  open well-typed-syntax-interpreter-full

  module inner (‘X’ : Type ε) (‘f’ : Term {ε ▻ (‘□’ ‘’ ⌜ ‘X’ ⌝ᵀ)} (W ‘X’)) where
    X : Set _
    X = Typeε⇓ ‘X’

    f'' : (x : Typeε⇓ (‘□’ ‘’ ⌜ ‘X’ ⌝ᵀ)) → Typeε▻⇓ {‘□’ ‘’ ⌜ ‘X’ ⌝ᵀ} (W ‘X’) x
    f'' = Termε▻⇓ ‘f’

    dummy : Type ε
    dummy = ‘Context’

    cast : (Γv : Σ Context Type) → Type (ε ▻ ‘Σ’ ‘Context’ ‘Type’)
    cast (Γ , v) = context-pick-if {P = Type} {Γ} (W dummy) v

    Hf : (h : Σ Context Type) → Type ε
    Hf h = (cast h ‘’ quote-sigma h ‘→'’ ‘X’)

    qh : Term {(ε ▻ ‘Σ’ ‘Context’ ‘Type’)} (W (‘Type’ ‘’ ‘ε’))
    qh = f' w‘‘’’ x
      where
        f' : Term (W (‘Type’ ‘’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Type’ ⌝ᶜ))
        f' = w→ ‘cast’ ‘'’ₐ ‘VAR₀’

        x : Term (W (‘Term’ ‘’₁ ⌜ ε ⌝ᶜ ‘’ ⌜ ‘Σ’ ‘Context’ ‘Type’ ⌝ᵀ))
        x = (w→ ‘quote-sigma’ ‘'’ₐ ‘VAR₀’)

    h2 : Type (ε ▻ ‘Σ’ ‘Context’ ‘Type’)
    h2 = (W₁ ‘□’ ‘’ (qh w‘‘→'’’ w ⌜ ‘X’ ⌝ᵀ))

    h : Σ Context Type
    h = ((ε ▻ ‘Σ’ ‘Context’ ‘Type’) , h2)

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

    toH-helper-helper : ∀ {k} → h2 ≡ k
      → □ (h2 ‘’ quote-sigma h ‘→'’ ‘□’ ‘’ ⌜ h2 ‘’ quote-sigma h ‘→'’ ‘X’ ⌝ᵀ)
      → □ (k ‘’ quote-sigma h ‘→'’ ‘□’ ‘’ ⌜ k ‘’ quote-sigma h ‘→'’ ‘X’ ⌝ᵀ)
    toH-helper-helper p x = transport (λ k → □ (k ‘’ quote-sigma h ‘→'’ ‘□’ ‘’ ⌜ k ‘’ quote-sigma h ‘→'’ ‘X’ ⌝ᵀ)) p x

    toH-helper : □ (cast h ‘’ quote-sigma h ‘→'’ ‘H’)
    toH-helper = toH-helper-helper
      {k = context-pick-if {P = Type} {ε ▻ ‘Σ’ ‘Context’ ‘Type’} (W dummy) h2}
      (sym (context-pick-if-refl {P = Type} {W dummy} {h2}))
      (S₀₀W₁'→ ((‘‘→'’’→w‘‘→'’’ ‘∘’ ‘‘fcomp-nd’’ ‘'’ₐ (‘s←←’ ‘‘∘’’ ‘cast-refl’ ‘‘∘’’ ⌜→'⌝ ‘'’ₐ ⌜ ‘λ’ ‘VAR₀’ ⌝ᵗ)) ‘∘’ ⌜←'⌝))

    ‘toH’ : □ (‘H'’ ‘→'’ ‘H’)
    ‘toH’ = ⌜→'⌝ ‘∘’ ‘‘fcomp-nd’’ ‘'’ₐ (⌜→'⌝ ‘'’ₐ ⌜ toH-helper ⌝ᵗ) ‘∘’ ⌜←'⌝

    toH : H' → H
    toH h' = toH-helper ‘∘’ h'

    fromH-helper-helper : ∀ {k} → h2 ≡ k
      → □ (‘□’ ‘’ ⌜ h2 ‘’ quote-sigma h ‘→'’ ‘X’ ⌝ᵀ ‘→'’ h2 ‘’ quote-sigma h)
      → □ (‘□’ ‘’ ⌜ k ‘’ quote-sigma h ‘→'’ ‘X’ ⌝ᵀ ‘→'’ k ‘’ quote-sigma h)
    fromH-helper-helper p x = transport (λ k → □ (‘□’ ‘’ ⌜ k ‘’ quote-sigma h ‘→'’ ‘X’ ⌝ᵀ ‘→'’ k ‘’ quote-sigma h)) p x

    fromH-helper : □ (‘H’ ‘→'’ cast h ‘’ quote-sigma h)
    fromH-helper = fromH-helper-helper
      {k = context-pick-if {P = Type} {ε ▻ ‘Σ’ ‘Context’ ‘Type’} (W dummy) h2}
      (sym (context-pick-if-refl {P = Type} {W dummy} {h2}))
      (S₀₀W₁'← (⌜→'⌝ ‘∘’ ‘‘fcomp-nd’’ ‘'’ₐ (⌜→'⌝ ‘'’ₐ ⌜ ‘λ’ ‘VAR₀’ ⌝ᵗ ‘‘∘’’ ‘cast-refl'’ ‘‘∘’’ ‘s→→’) ‘∘’ w‘‘→'’’→‘‘→'’’))

    ‘fromH’ : □ (‘H’ ‘→'’ ‘H'’)
    ‘fromH’ = ⌜→'⌝ ‘∘’ ‘‘fcomp-nd’’ ‘'’ₐ (⌜→'⌝ ‘'’ₐ ⌜ fromH-helper ⌝ᵗ) ‘∘’ ⌜←'⌝

    fromH : H → H'
    fromH h' = fromH-helper ‘∘’ h'

    lob : □ ‘X’
    lob = fromH h' ‘'’ₐ ⌜ h' ⌝ᵗ
      where
        f' : Term {ε ▻ ‘□’ ‘’ ‘H0’} (W (‘□’ ‘’ (⌜ ‘□’ ‘’ ‘H0’ ⌝ᵀ ‘‘→'’’ ⌜ ‘X’ ⌝ᵀ)))
        f' = Conv0 {‘H0’} {‘X’} (SW₁₀ (w∀ ‘fromH’ ‘’ₐ ‘VAR₀’))

        x : Term {ε ▻ ‘□’ ‘’ ‘H0’} (W (‘□’ ‘’ ⌜ ‘H’ ⌝ᵀ))
        x = w→ ‘quote-term’ ‘'’ₐ ‘VAR₀’

        h' : H
        h' = toH (‘λ’ (w→ (‘λ’ ‘f’) ‘'’ₐ (w→→ ‘tApp-nd’ ‘'’ₐ f' ‘'’ₐ x)))

  lob : {‘X’ : Type ε} → □ ((‘□’ ‘’ ⌜ ‘X’ ⌝ᵀ) ‘→'’ ‘X’) → □ ‘X’
  lob {‘X’} ‘f’ = inner.lob ‘X’ (un‘λ’ ‘f’)

\end{code}
