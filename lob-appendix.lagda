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
      _▻_ : (Γ : Context) → Typ Γ → Context

    data Typ : Context → Set where
      _‘’_ : ∀ {Γ A} → Typ (Γ ▻ A) → Term {Γ} A → Typ Γ
      _‘’₁_ : ∀ {Γ A B} → (C : Typ (Γ ▻ A ▻ B)) → (a : Term {Γ} A) → Typ (Γ ▻ B ‘’ a)
      _‘’₂_ : ∀ {Γ A B C} → (D : Typ (Γ ▻ A ▻ B ▻ C)) → (a : Term {Γ} A) → Typ (Γ ▻ B ‘’ a ▻ C ‘’₁ a)
      _‘’₃_ : ∀ {Γ A B C D} → (E : Typ (Γ ▻ A ▻ B ▻ C ▻ D)) → (a : Term {Γ} A) → Typ (Γ ▻ B ‘’ a ▻ C ‘’₁ a ▻ D ‘’₂ a)
      W : ∀ {Γ A} → Typ Γ → Typ (Γ ▻ A)
      W1 : ∀ {Γ A B} → Typ (Γ ▻ B) → Typ (Γ ▻ A ▻ (W {Γ = Γ} {A = A} B))
      W2 : ∀ {Γ A B C} → Typ (Γ ▻ B ▻ C) → Typ (Γ ▻ A ▻ W B ▻ W1 C)
      _‘→’_ : ∀ {Γ} (A : Typ Γ) → Typ (Γ ▻ A) → Typ Γ
      ‘Σ’ : ∀ {Γ} (T : Typ Γ) → Typ (Γ ▻ T) → Typ Γ
      ‘Context’ : ∀ {Γ} → Typ Γ
      ‘Typ’ : ∀ {Γ} → Typ (Γ ▻ ‘Context’)
      ‘Term’ : ∀ {Γ} → Typ (Γ ▻ ‘Context’ ▻ ‘Typ’)


    data Term : ∀ {Γ} → Typ Γ → Set where
      w : ∀ {Γ A B} → Term {Γ} B → Term {Γ = Γ ▻ A} (W {Γ = Γ} {A = A} B)
      ‘λ∙’ : ∀ {Γ A B} → Term {Γ = (Γ ▻ A)} B → Term {Γ} (A ‘→’ B)
      _‘’ₐ_ : ∀ {Γ A B} → (f : Term {Γ} (A ‘→’ B)) → (x : Term {Γ} A) → Term {Γ} (B ‘’ x)
      ‘VAR₀’ : ∀ {Γ T} → Term {Γ = Γ ▻ T} (W T)
      ⌜_⌝c : ∀ {Γ} → Context → Term {Γ} ‘Context’
      ⌜_⌝T : ∀ {Γ Γ'} → Typ Γ' → Term {Γ} (‘Typ’ ‘’ ⌜ Γ' ⌝c)
      ⌜_⌝t : ∀ {Γ Γ'} {T : Typ Γ'} → Term T → Term {Γ} (‘Term’ ‘’₁ ⌜ Γ' ⌝c ‘’ ⌜ T ⌝T)
      ‘quote-term’ : ∀ {Γ Γ'} {A : Typ Γ'} → Term {Γ} (‘Term’ ‘’₁ ⌜ Γ' ⌝c ‘’ ⌜ A ⌝T ‘→’ W (‘Term’ ‘’₁ ⌜ Γ ⌝c ‘’ ⌜ ‘Term’ ‘’₁ ⌜ Γ' ⌝c ‘’ ⌜ A ⌝T ⌝T))
      ‘quote-sigma’ : ∀ {Γ Γ'} → Term {Γ} (‘Σ’ ‘Context’ ‘Typ’ ‘→’ W (‘Term’ ‘’₁ ⌜ Γ' ⌝c ‘’ ⌜ ‘Σ’ ‘Context’ ‘Typ’ ⌝T))
      ‘cast’ : Term {ε} (‘Σ’ ‘Context’ ‘Typ’ ‘→’ W (‘Typ’ ‘’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c))
      SW : ∀ {Γ A B} {a : Term {Γ} A} → Term {Γ} (W B ‘’ a) → Term {Γ} B
      weakenTyp-substTyp-tProd : ∀ {Γ T T' A B} {a : Term {Γ} T} → Term {Γ = Γ ▻ T'} (W ((A ‘→’ B) ‘’ a)) → Term {Γ ▻ T'} (W ((A ‘’ a) ‘→’ (B ‘’₁ a)))
      substTyp-weakenTyp1-VAR₀ : ∀ {Γ A T} → Term {Γ ▻ A} (W1 T ‘’ ‘VAR₀’) → Term {Γ ▻ A} T
      weakenTyp-tProd : ∀ {Γ A B C} → Term {Γ = Γ ▻ C} (W (A ‘→’ B)) → Term {Γ = Γ ▻ C} (W A ‘→’ W1 B)
      weakenTyp-tProd-inv : ∀ {Γ A B C} → Term {Γ = Γ ▻ C} (W A ‘→’ W1 B) → Term {Γ = Γ ▻ C} (W (A ‘→’ B))
      weakenTyp-weakenTyp-tProd : ∀ {Γ A B C D} → Term {Γ ▻ C ▻ D} (W (W (A ‘→’ B))) → Term {Γ ▻ C ▻ D} (W (W A ‘→’ W1 B))
      substTyp1-tProd : ∀ {Γ T T' A B} {a : Term {Γ} T} → Term {Γ ▻ T' ‘’ a} ((A ‘→’ B) ‘’₁ a) → Term {Γ ▻ T' ‘’ a} ((A ‘’₁ a) ‘→’ (B ‘’₂ a))
      weakenTyp1-tProd : ∀ {Γ C D A B} → Term {Γ ▻ C ▻ W D} (W1 (A ‘→’ B)) → Term {Γ ▻ C ▻ W D} (W1 A ‘→’ W2 B)
      substTyp2-tProd : ∀ {Γ T T' T'' A B} {a : Term {Γ} T} → Term {Γ ▻ T' ‘’ a ▻ T'' ‘’₁ a} ((A ‘→’ B) ‘’₂ a) → Term {Γ ▻ T' ‘’ a ▻ T'' ‘’₁ a} ((A ‘’₂ a) ‘→’ (B ‘’₃ a))
      substTyp1-substTyp-weakenTyp-inv : ∀ {Γ C T A} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ} (A ‘’ a) → Term {Γ} (W A ‘’₁ a ‘’ b)
      substTyp1-substTyp-weakenTyp : ∀ {Γ C T A} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ} (W A ‘’₁ a ‘’ b) → Term {Γ} (A ‘’ a)
      weakenTyp-weakenTyp-substTyp1-substTyp-weakenTyp : ∀ {Γ C T A D E} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ ▻ D ▻ E} (W (W (W A ‘’₁ a ‘’ b))) → Term {Γ ▻ D ▻ E} (W (W (A ‘’ a)))
      weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp-inv : ∀ {Γ A B C T T'} {a : Term {Γ} A} {b : Term {Γ} (B ‘’ a)} {c : Term {Γ} (C ‘’₁ a ‘’ b)}
        → Term {Γ ▻ T'} (W (T ‘’₁ a ‘’ b))
        → Term {Γ ▻ T'} (W (W T ‘’₂ a ‘’₁ b ‘’ c))
      substTyp2-substTyp1-substTyp-weakenTyp : ∀ {Γ A B C T} {a : Term {Γ} A} {b : Term {Γ} (B ‘’ a)} {c : Term {Γ} (C ‘’₁ a ‘’ b)}
        → Term {Γ} (W T ‘’₂ a ‘’₁ b ‘’ c)
        → Term {Γ} (T ‘’₁ a ‘’ b)
      weakenTyp-substTyp2-substTyp1-substTyp-tProd : ∀ {Γ T T' T'' T''' A B} {a : Term {Γ} T} {b : Term {Γ} (T' ‘’ a)} {c : Term {Γ} (T'' ‘’₁ a ‘’ b)}
        → Term {Γ ▻ T'''} (W ((A ‘→’ B) ‘’₂ a ‘’₁ b ‘’ c))
        → Term {Γ ▻ T'''} ((W (A ‘’₂ a ‘’₁ b ‘’ c)) ‘→’ (W1 (B ‘’₃ a ‘’₂ b ‘’₁ c)))
      weakenTyp2-weakenTyp1 : ∀ {Γ A B C D} → Term {Γ ▻ A ▻ W B ▻ W1 C} (W2 (W D)) → Term {Γ ▻ A ▻ W B ▻ W1 C} (W (W1 D))
      weakenTyp1-weakenTyp : ∀ {Γ A B C} → Term {Γ ▻ A ▻ W B} (W1 (W C)) → Term {Γ ▻ A ▻ W B} (W (W C))
      weakenTyp1-weakenTyp-inv : ∀ {Γ A B C} → Term {Γ ▻ A ▻ W B} (W (W C)) → Term {Γ ▻ A ▻ W B} (W1 (W C))
      weakenTyp1-weakenTyp1-weakenTyp : ∀ {Γ A B C T} → Term {Γ ▻ A ▻ B ▻ W (W C)} (W1 (W1 (W T))) → Term {Γ ▻ A ▻ B ▻ W (W C)} (W1 (W (W T)))
      substTyp1-weakenTyp1 : ∀ {Γ A B C} {a : Term {Γ} A} → Term {Γ ▻ W B ‘’ a} (W1 C ‘’₁ a) → Term {Γ ▻ B} C
      weakenTyp1-substTyp-weakenTyp1-inv : ∀ {Γ A T'' T' T} {a : Term {Γ} A}
        → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W1 (W (T ‘’ a)))
        → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W1 (W T ‘’₁ a))
      weakenTyp1-substTyp-weakenTyp1 : ∀ {Γ A T'' T' T} {a : Term {Γ} A}
        → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W1 (W T ‘’₁ a))
        → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W1 (W (T ‘’ a)))
      weakenTyp-substTyp-substTyp-weakenTyp1 : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Typ (Γ ▻ A)}
        → Term {Γ ▻ T'} (W (W1 T ‘’ a ‘’ b))
        → Term {Γ ▻ T'} (W (T ‘’ (SW ((‘λ∙’ a) ‘’ₐ b))))
      weakenTyp-substTyp-substTyp-weakenTyp1-inv : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Typ (Γ ▻ A)}
        → Term {Γ ▻ T'} (W (T ‘’ (SW ((‘λ∙’ a) ‘’ₐ b))))
        → Term {Γ ▻ T'} (W (W1 T ‘’ a ‘’ b))
      substTyp-weakenTyp1-weakenTyp : ∀ {Γ T} {A : Typ Γ} {B : Typ Γ}
        → {a : Term {Γ = Γ ▻ T} (W {Γ = Γ} {A = T} B)}
        → Term {Γ = Γ ▻ T} (W1 (W A) ‘’ a)
        → Term {Γ = Γ ▻ T} (W A)
      substTyp3-substTyp2-substTyp1-substTyp-weakenTyp : ∀ {Γ A B C D T T'} {a : Term {Γ} A} {b : Term {Γ} (B ‘’ a)} {c : Term {Γ} (C ‘’₁ a ‘’ b)}
           {d : Term {Γ = (Γ ▻ T')} (W (D ‘’₂ a ‘’₁ b ‘’ c))}
           → Term {Γ = (Γ ▻ T')} (W1 (W T ‘’₃ a ‘’₂ b ‘’₁ c) ‘’ d)
           → Term {Γ = (Γ ▻ T')} (W (T ‘’₂ a ‘’₁ b ‘’ c))
      weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp1 : ∀ {Γ A B C T T'} {a : Term {Γ} A} {b : Term (B ‘’ a)} {c : Term (C ‘’ a)}
        → Term {Γ = (Γ ▻ T')} (W (W1 T ‘’₂ a ‘’₁ b ‘’ substTyp1-substTyp-weakenTyp-inv c))
        → Term {Γ = (Γ ▻ T')} (W (T ‘’₁ a ‘’ c))
      substTyp1-substTyp-tProd : ∀ {Γ T T' A B a b} → Term ((_‘→’_ {Γ = Γ ▻ T ▻ T'} A B) ‘’₁ a ‘’ b) → Term (_‘→’_ {Γ = Γ} (A ‘’₁ a ‘’ b) (B ‘’₂ a ‘’₁ b))
      substTyp2-substTyp-substTyp-weakenTyp1-weakenTyp-weakenTyp : ∀ {Γ A} {T : Typ (Γ ▻ A)} {T' C B} {a : Term {Γ} A} {b : Term {Γ = (Γ ▻ C ‘’ a)} (B ‘’₁ a)}
           {c : Term {Γ = (Γ ▻ T')} (W (C ‘’ a))}
           → Term {Γ = (Γ ▻ T')} (W1 (W (W T) ‘’₂ a ‘’ b) ‘’ c)
           → Term {Γ = (Γ ▻ T')} (W (T ‘’ a))
      substTyp1-substTyp-weakenTyp2-weakenTyp : ∀ {Γ T' A B T} {a : Term {Γ ▻ T'} (W A)} {b : Term {Γ ▻ T'} (W1 B ‘’ a)}
        → Term {Γ ▻ T'} (W2 (W T) ‘’₁ a ‘’ b)
        → Term {Γ ▻ T'} (W1 T ‘’ a)
      weakenTyp-weakenTyp1-weakenTyp : ∀ {Γ A B C D} → Term {Γ ▻ A ▻ W B ▻ W1 C} (W (W1 (W D))) → Term {Γ ▻ A ▻ W B ▻ W1 C} (W (W (W D)))
      beta-under-subst : ∀ {Γ A B B'} {g : Term {Γ} (A ‘→’ W B)} {x : Term {Γ} A}
        → Term (B' ‘’ SW (‘λ∙’ (SW (‘λ∙’ (weakenTyp1-weakenTyp (substTyp-weakenTyp1-VAR₀ (weakenTyp-tProd (w (weakenTyp-tProd (w g))) ‘’ₐ ‘VAR₀’))) ‘’ₐ ‘VAR₀’)) ‘’ₐ x))
        → Term (B' ‘’ SW (g ‘’ₐ x))
      ‘proj₁'’ : ∀ {Γ} {T : Typ Γ} {P : Typ (Γ ▻ T)} → Term (‘Σ’ T P ‘→’ W T)
      ‘proj₂'’ : ∀ {Γ} {T : Typ Γ} {P : Typ (Γ ▻ T)} → Term {Γ ▻ ‘Σ’ T P} (W1 P ‘’ SW (‘λ∙’ (weakenTyp1-weakenTyp (substTyp-weakenTyp1-VAR₀ (weakenTyp-tProd (w (weakenTyp-tProd (w ‘proj₁'’))) ‘’ₐ ‘VAR₀’))) ‘’ₐ ‘VAR₀’))
      ‘existT’ : ∀ {Γ T P} (x : Term {Γ} T) (p : Term (P ‘’ x)) → Term (‘Σ’ T P)
      {- these are redundant, but useful for not having to normalize the subsequent ones -}
      _‘‘’’_ : ∀ {Γ} {A : Typ Γ}
        → Term {ε} (‘Typ’ ‘’ ⌜ Γ ▻ A ⌝c)
        → Term {ε} (‘Term’ ‘’₁ ⌜ Γ ⌝c ‘’ ⌜ A ⌝T)
        → Term {ε} (‘Typ’ ‘’ ⌜ Γ ⌝c)
      _w‘‘’’_ : ∀ {X Γ} {A : Typ Γ}
        → Term {ε ▻ X} (W (‘Typ’ ‘’ ⌜ Γ ▻ A ⌝c))
        → Term {ε ▻ X} (W (‘Term’ ‘’₁ ⌜ Γ ⌝c ‘’ ⌜ A ⌝T))
        → Term {ε ▻ X} (W (‘Typ’ ‘’ ⌜ Γ ⌝c))
      _‘‘→'’’_ : ∀ {Γ}
        → Term {ε} (‘Typ’ ‘’ Γ)
        → Term {ε} (‘Typ’ ‘’ Γ)
        → Term {ε} (‘Typ’ ‘’ Γ)
      _w‘‘→'’’_ : ∀ {X Γ}
        → Term {ε ▻ X} (W (‘Typ’ ‘’ Γ))
        → Term {ε ▻ X} (W (‘Typ’ ‘’ Γ))
        → Term {ε ▻ X} (W (‘Typ’ ‘’ Γ))
      w→ : ∀ {Γ A B C} → Term (A ‘→’ W B) → Term {Γ = Γ ▻ C} (W A ‘→’ W (W B))
      {- things that were postulates, but are no longer -}
      ‘‘→'’’→w‘‘→'’’ : ∀ {T'}
           {b : Term {ε} (‘Typ’ ‘’ ⌜ ε ⌝c)}
           {c : Term {ε ▻ T'} (W (‘Typ’ ‘’ ⌜ ε ⌝c))}
           {e : Term {ε} T'}
           → Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ (SW (‘λ∙’ (c w‘‘→'’’ w b) ‘’ₐ e))
                      ‘→’ W (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ (SW (‘λ∙’ c ‘’ₐ e) ‘‘→'’’ b)))
      w‘‘→'’’→‘‘→'’’ : ∀ {T'}
           {b : Term {ε} (‘Typ’ ‘’ ⌜ ε ⌝c)}
           {c : Term {ε ▻ T'} (W (‘Typ’ ‘’ ⌜ ε ⌝c))}
           {e : Term {ε} T'}
           → Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ (SW (‘λ∙’ c ‘’ₐ e) ‘‘→'’’ b)
                      ‘→’ W (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ (SW (‘λ∙’ (c w‘‘→'’’ w b) ‘’ₐ e))))
      ‘tApp-nd’ : ∀ {Γ} {A : Term {ε} (‘Typ’ ‘’ Γ)} {B : Term {ε} (‘Typ’ ‘’ Γ)} →
        Term {ε} (‘Term’ ‘’₁ Γ ‘’ (A ‘‘→'’’ B)
             ‘→’ W (‘Term’ ‘’₁ Γ ‘’ A
             ‘→’ W (‘Term’ ‘’₁ Γ ‘’ B)))
      ⌜←'⌝ : ∀ {H X} →
        Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ (⌜ H ⌝T ‘‘→'’’ ⌜ X ⌝T)
             ‘→’ W (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ ⌜ H ‘→’ W X ⌝T))
      ⌜→'⌝ : ∀ {H X} →
        Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ ⌜ H ‘→’ W X ⌝T
             ‘→’ W (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ (⌜ H ⌝T ‘‘→'’’ ⌜ X ⌝T)))
      ‘‘fcomp-nd’’ : ∀ {A B C} →
        Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ (A ‘‘→'’’ C)
             ‘→’ W (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ (C ‘‘→'’’ B)
             ‘→’ W (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ (A ‘‘→'’’ B))))
      ⌜‘’⌝ : ∀ {B A} {b : Term {ε} B} →
          Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’
              (⌜ A ‘’ b ⌝T ‘‘→'’’ ⌜ A ⌝T ‘‘’’ ⌜ b ⌝t))
      ⌜‘’⌝' : ∀ {B A} {b : Term {ε} B} →
          Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’
              (⌜ A ⌝T ‘‘’’ ⌜ b ⌝t ‘‘→'’’ ⌜ A ‘’ b ⌝T))
      ‘cast-refl’ : ∀ {T : Typ (ε ▻ ‘Σ’ ‘Context’ ‘Typ’)} →
          Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’
              ((⌜ T ‘’ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c ⌜ T ⌝T ⌝T)
                 ‘‘→'’’
                 (SW (‘cast’ ‘’ₐ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c ⌜ T ⌝T)
                   ‘‘’’ SW (‘quote-sigma’ ‘’ₐ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c ⌜ T ⌝T))))
      ‘cast-refl'’ : ∀ {T : Typ (ε ▻ ‘Σ’ ‘Context’ ‘Typ’)} →
          Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’
              ((SW (‘cast’ ‘’ₐ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c ⌜ T ⌝T)
                   ‘‘’’ SW (‘quote-sigma’ ‘’ₐ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c ⌜ T ⌝T))
                 ‘‘→'’’
                 (⌜ T ‘’ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c ⌜ T ⌝T ⌝T)))
      ‘s→→’ : ∀ {T B}
             {b : Term {ε} (T ‘→’ W (‘Typ’ ‘’ ⌜ ε ▻ B ⌝c))}
             {c : Term {ε} (T ‘→’ W (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ ⌜ B ⌝T))}
             {v : Term {ε} T} →
        (Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c
             ‘’ ((SW (((‘λ∙’ (SW (w→ b ‘’ₐ ‘VAR₀’) w‘‘’’ SW (w→ c ‘’ₐ ‘VAR₀’)) ‘’ₐ v))))
                   ‘‘→'’’ (SW (b ‘’ₐ v) ‘‘’’ SW (c ‘’ₐ v)))))
      ‘s←←’ : ∀ {T B}
             {b : Term {ε} (T ‘→’ W (‘Typ’ ‘’ ⌜ ε ▻ B ⌝c))}
             {c : Term {ε} (T ‘→’ W (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ ⌜ B ⌝T))}
             {v : Term {ε} T} →
        (Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c
             ‘’ ((SW (b ‘’ₐ v) ‘‘’’ SW (c ‘’ₐ v))
                   ‘‘→'’’ (SW (((‘λ∙’ (SW (w→ b ‘’ₐ ‘VAR₀’) w‘‘’’ SW (w→ c ‘’ₐ ‘VAR₀’)) ‘’ₐ v)))))))

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

  WS∀ : ∀ {Γ T T' A B} {a : Term {Γ = Γ} T} → Term {Γ = Γ ▻ T'} (W ((A ‘→’ B) ‘’ a)) → Term {Γ ▻ T'} (W ((A ‘’ a) ‘→’ (B ‘’₁ a)))
  WS∀ = weakenTyp-substTyp-tProd

  _‘→'’_ : ∀ {Γ} → Typ Γ → Typ Γ → Typ Γ
  _‘→'’_ {Γ = Γ} A B = _‘→’_ {Γ = Γ} A (W {Γ = Γ} {A = A} B)

  _‘'’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→'’ B) → Term A → Term B
  _‘'’ₐ_ {Γ} {A} {B} f x = SW (_‘’ₐ_ {Γ} {A} {W B} f x)

  _‘t’_ : ∀ {Γ A} {B : Typ (Γ ▻ A)} → (b : Term {Γ = Γ ▻ A} B) → (a : Term {Γ} A) → Term {Γ} (B ‘’ a)
  b ‘t’ a = ‘λ∙’ b ‘’ₐ a

  substTyp-tProd : ∀ {Γ T A B} {a : Term {Γ} T} →
                           Term {Γ} ((A ‘→’ B) ‘’ a)
                           → Term {Γ} (_‘→’_ {Γ = Γ} (A ‘’ a) (B ‘’₁ a))
  substTyp-tProd {Γ} {T} {A} {B} {a} x = SW ((WS∀ (w x)) ‘t’ a)

  S∀ = substTyp-tProd

  ‘λ'∙’ : ∀ {Γ A B} → Term {Γ ▻ A} (W B) -> Term (A ‘→'’ B)
  ‘λ'∙’ f = ‘λ∙’ f

  SW1V : ∀ {Γ A T} → Term {Γ ▻ A} (W1 T ‘’ ‘VAR₀’) → Term {Γ ▻ A} T
  SW1V = substTyp-weakenTyp1-VAR₀

  S₁∀ : ∀ {Γ T T' A B} {a : Term {Γ} T} → Term {Γ ▻ T' ‘’ a} ((A ‘→’ B) ‘’₁ a) → Term {Γ ▻ T' ‘’ a} ((A ‘’₁ a) ‘→’ (B ‘’₂ a))
  S₁∀ = substTyp1-tProd

  un‘λ∙’ : ∀ {Γ A B} → Term (A ‘→’ B) → Term {Γ ▻ A} B
  un‘λ∙’ f = SW1V (weakenTyp-tProd (w f) ‘’ₐ ‘VAR₀’)

  weakenProd : ∀ {Γ A B C} →
                            Term {Γ} (A ‘→’ B)
                            → Term {Γ = Γ ▻ C} (W A ‘→’ W1 B)
  weakenProd {Γ} {A} {B} {C} x = weakenTyp-tProd (w x)
  w∀ = weakenProd

  w1 : ∀ {Γ A B C} → Term {Γ = Γ ▻ B} C → Term {Γ = Γ ▻ A ▻ W {Γ = Γ} {A = A} B} (W1 {Γ = Γ} {A = A} {B = B} C)
  w1 x = un‘λ∙’ (weakenTyp-tProd (w (‘λ∙’ x)))

  _‘t’₁_ : ∀ {Γ A B C} → (c : Term {Γ = Γ ▻ A ▻ B} C) → (a : Term {Γ} A) → Term {Γ = Γ ▻ B ‘’ a} (C ‘’₁ a)
  f ‘t’₁ x = un‘λ∙’ (S∀ (‘λ∙’ (‘λ∙’ f) ‘’ₐ x))
  _‘t’₂_ : ∀ {Γ A B C D} → (c : Term {Γ = Γ ▻ A ▻ B ▻ C} D) → (a : Term {Γ} A) → Term {Γ = Γ ▻ B ‘’ a ▻ C ‘’₁ a} (D ‘’₂ a)
  f ‘t’₂ x = un‘λ∙’ (S₁∀ (un‘λ∙’ (S∀ (‘λ∙’ (‘λ∙’ (‘λ∙’ f)) ‘’ₐ x))))

  S₁₀W' : ∀ {Γ C T A} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ} (A ‘’ a) → Term {Γ} (W A ‘’₁ a ‘’ b)
  S₁₀W' = substTyp1-substTyp-weakenTyp-inv

  S₁₀W : ∀ {Γ C T A} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ} (W A ‘’₁ a ‘’ b) → Term {Γ} (A ‘’ a)
  S₁₀W = substTyp1-substTyp-weakenTyp

  substTyp1-substTyp-weakenTyp-weakenTyp : ∀ {Γ T A} {B : Typ (Γ ▻ A)}
      → {a : Term {Γ} A}
      → {b : Term {Γ} (B ‘’ a)}
      → Term {Γ} (W (W T) ‘’₁ a ‘’ b)
      → Term {Γ} T
  substTyp1-substTyp-weakenTyp-weakenTyp x = SW (S₁₀W x)

  S₁₀WW = substTyp1-substTyp-weakenTyp-weakenTyp


  S₂₁₀W : ∀ {Γ A B C T} {a : Term {Γ} A} {b : Term {Γ} (B ‘’ a)} {c : Term {Γ} (C ‘’₁ a ‘’ b)}
        → Term {Γ} (W T ‘’₂ a ‘’₁ b ‘’ c)
        → Term {Γ} (T ‘’₁ a ‘’ b)
  S₂₁₀W = substTyp2-substTyp1-substTyp-weakenTyp

  substTyp2-substTyp1-substTyp-weakenTyp-weakenTyp : ∀ {Γ A B C T}
           {a : Term {Γ} A}
           {b : Term {Γ} (B ‘’ a)}
           {c : Term {Γ} (C ‘’₁ a ‘’ b)} →
      Term {Γ} (W (W T) ‘’₂ a ‘’₁ b ‘’ c)
      → Term {Γ} (T ‘’ a)
  substTyp2-substTyp1-substTyp-weakenTyp-weakenTyp x = S₁₀W (S₂₁₀W x)

  S₂₁₀WW = substTyp2-substTyp1-substTyp-weakenTyp-weakenTyp

  W1W : ∀ {Γ A B C} → Term {Γ ▻ A ▻ W B} (W1 (W C)) → Term {Γ ▻ A ▻ W B} (W (W C))
  W1W = weakenTyp1-weakenTyp

  W1W1W : ∀ {Γ A B C T} → Term {Γ ▻ A ▻ B ▻ W (W C)} (W1 (W1 (W T))) → Term {Γ ▻ A ▻ B ▻ W (W C)} (W1 (W (W T)))
  W1W1W = weakenTyp1-weakenTyp1-weakenTyp

  weakenTyp-tProd-nd : ∀ {Γ A B C} →
                            Term {Γ = Γ ▻ C} (W (A ‘→'’ B))
                            → Term {Γ = Γ ▻ C} (W A ‘→'’ W B)
  weakenTyp-tProd-nd x = ‘λ'∙’ (W1W (SW1V (weakenTyp-tProd (w (weakenTyp-tProd x)) ‘’ₐ ‘VAR₀’)))

  weakenProd-nd : ∀ {Γ A B C} →
                               Term (A ‘→'’ B)
                               → Term {Γ = Γ ▻ C} (W A ‘→'’ W B)
  weakenProd-nd {Γ} {A} {B} {C} x = weakenTyp-tProd-nd (w x)




  weakenTyp-tProd-nd-tProd-nd : ∀ {Γ A B C D} →
      Term {Γ = Γ ▻ D} (W (A ‘→'’ B ‘→'’ C))
      → Term {Γ = Γ ▻ D} (W A ‘→'’ W B ‘→'’ W C)
  weakenTyp-tProd-nd-tProd-nd x = ‘λ∙’ (weakenTyp-tProd-inv (‘λ∙’ (W1W1W (SW1V (w∀ (weakenTyp-tProd (weakenTyp-weakenTyp-tProd (w→ (weakenTyp-tProd-nd x) ‘'’ₐ ‘VAR₀’))) ‘’ₐ ‘VAR₀’)))))

  weakenProd-nd-Prod-nd : ∀ {Γ A B C D} →
      Term (A ‘→'’ B ‘→'’ C)
      → Term {Γ = Γ ▻ D} (W A ‘→'’ W B ‘→'’ W C)
  weakenProd-nd-Prod-nd {Γ} {A} {B} {C} {D} x = weakenTyp-tProd-nd-tProd-nd (w x)
  w→→ = weakenProd-nd-Prod-nd

  S₁W1 : ∀ {Γ A B C} {a : Term {Γ} A} → Term {Γ ▻ W B ‘’ a} (W1 C ‘’₁ a) → Term {Γ ▻ B} C
  S₁W1 = substTyp1-weakenTyp1


  W1S₁W' : ∀ {Γ A T'' T' T} {a : Term {Γ} A}
        → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W1 (W (T ‘’ a)))
        → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W1 (W T ‘’₁ a))
  W1S₁W' = weakenTyp1-substTyp-weakenTyp1-inv


  substTyp-weakenTyp1-inv : ∀ {Γ A T' T}
           {a : Term {Γ} A} →
      Term {Γ = (Γ ▻ T' ‘’ a)} (W (T ‘’ a))
      → Term {Γ = (Γ ▻ T' ‘’ a)} (W T ‘’₁ a)
  substTyp-weakenTyp1-inv {a = a} x = S₁W1 (W1S₁W' (w1 x) ‘t’₁ a)

  S₁W' = substTyp-weakenTyp1-inv

  _‘∘’_ : ∀ {Γ A B C}
      → Term {Γ} (A ‘→'’ B)
      → Term {Γ} (B ‘→'’ C)
      → Term {Γ} (A ‘→'’ C)
  g ‘∘’ f = ‘λ∙’ (w→ f ‘'’ₐ (w→ g ‘'’ₐ ‘VAR₀’))


  WS₀₀W1 : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Typ (Γ ▻ A)}
        → Term {Γ ▻ T'} (W (W1 T ‘’ a ‘’ b))
        → Term {Γ ▻ T'} (W (T ‘’ (SW (a ‘t’ b))))
  WS₀₀W1 = weakenTyp-substTyp-substTyp-weakenTyp1

  WS₀₀W1' : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Typ (Γ ▻ A)}
        → Term {Γ ▻ T'} (W (T ‘’ (SW (a ‘t’ b))))
        → Term {Γ ▻ T'} (W (W1 T ‘’ a ‘’ b))
  WS₀₀W1' = weakenTyp-substTyp-substTyp-weakenTyp1-inv

  substTyp-substTyp-weakenTyp1-inv-arr : ∀ {Γ B A}
           {b : Term {Γ} B}
           {a : Term {Γ ▻ B} (W A)}
           {T : Typ (Γ ▻ A)}
           {X} →
      Term {Γ} (T ‘’ (SW (a ‘t’ b)) ‘→'’ X)
      → Term {Γ} (W1 T ‘’ a ‘’ b ‘→'’ X)
  substTyp-substTyp-weakenTyp1-inv-arr x = ‘λ∙’ (w→ x ‘'’ₐ WS₀₀W1 ‘VAR₀’)

  S₀₀W1'→ = substTyp-substTyp-weakenTyp1-inv-arr

  substTyp-substTyp-weakenTyp1-arr-inv : ∀ {Γ B A}
           {b : Term {Γ} B}
           {a : Term {Γ ▻ B} (W A)}
           {T : Typ (Γ ▻ A)}
           {X} →
      Term {Γ} (X ‘→'’ T ‘’ (SW (a ‘t’ b)))
      → Term {Γ} (X ‘→'’ W1 T ‘’ a ‘’ b)
  substTyp-substTyp-weakenTyp1-arr-inv x = ‘λ∙’ (WS₀₀W1' (un‘λ∙’ x))

  S₀₀W1'← = substTyp-substTyp-weakenTyp1-arr-inv


  substTyp-substTyp-weakenTyp1 : ∀ {Γ B A}
           {b : Term {Γ} B}
           {a : Term {Γ ▻ B} (W A)}
           {T : Typ (Γ ▻ A)} →
      Term {Γ} (W1 T ‘’ a ‘’ b)
      → Term {Γ} (T ‘’ (SW (a ‘t’ b)))
  substTyp-substTyp-weakenTyp1 x = (SW (WS₀₀W1 (w x) ‘t’ x))
  S₀₀W1 = substTyp-substTyp-weakenTyp1

  SW1W : ∀ {Γ T} {A : Typ Γ} {B : Typ Γ}
        → {a : Term {Γ = Γ ▻ T} (W {Γ = Γ} {A = T} B)}
        → Term {Γ = Γ ▻ T} (W1 (W A) ‘’ a)
        → Term {Γ = Γ ▻ T} (W A)
  SW1W = substTyp-weakenTyp1-weakenTyp


  S₂₀₀W1WW : ∀ {Γ A} {T : Typ (Γ ▻ A)} {T' C B} {a : Term {Γ} A} {b : Term {Γ = (Γ ▻ C ‘’ a)} (B ‘’₁ a)}
           {c : Term {Γ = (Γ ▻ T')} (W (C ‘’ a))}
           → Term {Γ = (Γ ▻ T')} (W1 (W (W T) ‘’₂ a ‘’ b) ‘’ c)
           → Term {Γ = (Γ ▻ T')} (W (T ‘’ a))
  S₂₀₀W1WW = substTyp2-substTyp-substTyp-weakenTyp1-weakenTyp-weakenTyp


  S₁₀W2W : ∀ {Γ T' A B T} {a : Term {Γ ▻ T'} (W A)} {b : Term {Γ ▻ T'} (W1 B ‘’ a)}
        → Term {Γ ▻ T'} (W2 (W T) ‘’₁ a ‘’ b)
        → Term {Γ ▻ T'} (W1 T ‘’ a)
  S₁₀W2W = substTyp1-substTyp-weakenTyp2-weakenTyp
\end{code}

\begin{code}
 module well-typed-syntax-context-helpers where
  open well-typed-syntax
  open well-typed-syntax-helpers

  □_ : Typ ε → Set
  □_ T = Term {Γ = ε} T
\end{code}

\begin{code}
 module well-typed-quoted-syntax-defs where
  open well-typed-syntax
  open well-typed-syntax-helpers
  open well-typed-syntax-context-helpers

  ‘ε’ : Term {Γ = ε} ‘Context’
  ‘ε’ = ⌜ ε ⌝c

  ‘□’ : Typ (ε ▻ ‘Typ’ ‘’ ‘ε’)
  ‘□’ = ‘Term’ ‘’₁ ‘ε’

\end{code}

\begin{code}
 module well-typed-syntax-eq-dec where
  open well-typed-syntax

  context-pick-if : ∀ {ℓ} {P : Context → Set ℓ}
                          {Γ : Context}
                          (dummy : P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’))
                          (val : P Γ) →
                        P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’)
  context-pick-if {P = P} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} dummy val = val
  context-pick-if {P = P} {Γ} dummy val = dummy

  context-pick-if-refl : ∀ {ℓ P dummy val} →
                             context-pick-if {ℓ} {P} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} dummy val ≡ val
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

  quote-sigma : (Γv : Σ Context Typ) → Term {ε} (‘Σ’ ‘Context’ ‘Typ’)
  quote-sigma (Γ , v) = ‘existT’ ⌜ Γ ⌝c ⌜ v ⌝T

  _‘‘∘’’_ : ∀ {A B C}
      → □ (‘□’ ‘’ (C ‘‘→'’’ B))
      → □ (‘□’ ‘’ (A ‘‘→'’’ C))
      → □ (‘□’ ‘’ (A ‘‘→'’’ B))
  g ‘‘∘’’ f = (‘‘fcomp-nd’’ ‘'’ₐ f ‘'’ₐ g)

  Conv0 : ∀ {qH0 qX} →
      Term {Γ = (ε ▻ ‘□’ ‘’ qH0)}
            (W (‘□’ ‘’ ⌜ ‘□’ ‘’ qH0 ‘→'’ qX ⌝T))
      → Term {Γ = (ε ▻ ‘□’ ‘’ qH0)}
               (W
                  (‘□’ ‘’ (⌜ ‘□’ ‘’ qH0 ⌝T ‘‘→'’’ ⌜ qX ⌝T)))
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
                            (dummy : P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’))
                            (val : P Γ) →
                          P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’))
    (context-pick-if-refl' : ∀ ℓ P dummy val →
                              context-pick-if' ℓ P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’) dummy val ≡ val)
    where

    context-pick-if : ∀ {ℓ} {P : Context → Set ℓ}
                            {Γ : Context}
                            (dummy : P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’))
                            (val : P Γ) →
                          P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’)
    context-pick-if {P = P} dummy val = context-pick-if' _ P _ dummy val
    context-pick-if-refl : ∀ {ℓ P dummy val} →
                              context-pick-if {ℓ} {P} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} dummy val ≡ val
    context-pick-if-refl {P = P} = context-pick-if-refl' _ P _ _

    private
      dummy : Typ ε
      dummy = ‘Context’

    cast-helper : ∀ {X T A} {x : Term X} → A ≡ T → Term {ε} (T ‘’ x ‘→'’ A ‘’ x)
    cast-helper refl = ‘λ∙’ ‘VAR₀’

    cast'-proof : ∀ {T} → Term {ε} (context-pick-if {P = Typ} (W dummy) T ‘’ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c ⌜ T ⌝T
                  ‘→'’ T ‘’ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c ⌜ T ⌝T)
    cast'-proof {T} = cast-helper {‘Σ’ ‘Context’ ‘Typ’}
                        {context-pick-if {P = Typ} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} (W dummy) T}
                        {T} (sym (context-pick-if-refl {P = Typ} {dummy = W dummy}))

    cast-proof : ∀ {T} → Term {ε} (T ‘’ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c ⌜ T ⌝T
                  ‘→'’ context-pick-if {P = Typ} (W dummy) T ‘’ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c ⌜ T ⌝T)
    cast-proof {T} = cast-helper {‘Σ’ ‘Context’ ‘Typ’} {T}
                        {context-pick-if {P = Typ} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} (W dummy) T}
                        (context-pick-if-refl {P = Typ} {dummy = W dummy})

    ‘idfun’ : ∀ {T} → Term {ε} (T ‘→'’ T)
    ‘idfun’ = ‘λ∙’ ‘VAR₀’

    mutual
      Context⇓ : (Γ : Context) → Set (lsuc max-level)
      Typ⇓ : {Γ : Context} → Typ Γ → Context⇓ Γ → Set max-level

      Context⇓ ε = ⊤
      Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (λ Γ' → Typ⇓ T Γ')

      Typ⇓ (T₁ ‘’ x) Γ⇓ = Typ⇓ T₁ (Γ⇓ , Term⇓ x Γ⇓)
      Typ⇓ (T₂ ‘’₁ a) (Γ⇓ , A⇓) = Typ⇓ T₂ ((Γ⇓ , Term⇓ a Γ⇓) , A⇓)
      Typ⇓ (T₃ ‘’₂ a) ((Γ⇓ , A⇓) , B⇓) = Typ⇓ T₃ (((Γ⇓ , Term⇓ a Γ⇓) , A⇓) , B⇓)
      Typ⇓ (T₃ ‘’₃ a) (((Γ⇓ , A⇓) , B⇓) , C⇓) = Typ⇓ T₃ ((((Γ⇓ , Term⇓ a Γ⇓) , A⇓) , B⇓) , C⇓)
      Typ⇓ (W T₁) (Γ⇓ , _) = Typ⇓ T₁ Γ⇓
      Typ⇓ (W1 T₂) ((Γ⇓ , A⇓) , B⇓) = Typ⇓ T₂ (Γ⇓ , B⇓)
      Typ⇓ (W2 T₃) (((Γ⇓ , A⇓) , B⇓) , C⇓) = Typ⇓ T₃ ((Γ⇓ , B⇓) , C⇓)
      Typ⇓ (T ‘→’ T₁) Γ⇓ = (T⇓ : Typ⇓ T Γ⇓) → Typ⇓ T₁ (Γ⇓ , T⇓)
      Typ⇓ ‘Context’ Γ⇓ = Lifted Context
      Typ⇓ ‘Typ’ (Γ⇓ , T⇓) = Lifted (Typ (lower T⇓))
      Typ⇓ ‘Term’ (Γ⇓ , T⇓ , t⇓) = Lifted (Term (lower t⇓))
      Typ⇓ (‘Σ’ T T₁) Γ⇓ = Σ (Typ⇓ T Γ⇓) (λ T⇓ → Typ⇓ T₁ (Γ⇓ , T⇓))

      Term⇓ : ∀ {Γ : Context} {T : Typ Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Typ⇓ T Γ⇓
      Term⇓ (w t) (Γ⇓ , A⇓) = Term⇓ t Γ⇓
      Term⇓ (‘λ∙’ t) Γ⇓ T⇓ = Term⇓ t (Γ⇓ , T⇓)
      Term⇓ (t ‘’ₐ t₁) Γ⇓ = Term⇓ t Γ⇓ (Term⇓ t₁ Γ⇓)
      Term⇓ ‘VAR₀’ (Γ⇓ , A⇓) = A⇓
      Term⇓ (⌜ Γ ⌝c) Γ⇓ = lift Γ
      Term⇓ (⌜ T ⌝T) Γ⇓ = lift T
      Term⇓ (⌜ t ⌝t) Γ⇓ = lift t
      Term⇓ ‘quote-term’ Γ⇓ (lift T⇓) = lift ⌜ T⇓ ⌝t
      Term⇓ (‘quote-sigma’ {Γ₀} {Γ₁}) Γ⇓ (lift Γ , lift T) = lift (‘existT’ {Γ₁} ⌜ Γ ⌝c ⌜ T ⌝T)
      Term⇓ ‘cast’ Γ⇓ T⇓ = lift (context-pick-if
                                {P = Typ}
                                {lower (Σ.proj₁ T⇓)}
                                (W dummy)
                                (lower (Σ.proj₂ T⇓)))
      Term⇓ (SW t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (weakenTyp-substTyp-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
      Term⇓ (substTyp-weakenTyp1-VAR₀ t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (weakenTyp-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
      Term⇓ (weakenTyp-tProd-inv t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
      Term⇓ (weakenTyp-weakenTyp-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
      Term⇓ (substTyp1-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
      Term⇓ (weakenTyp1-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
      Term⇓ (substTyp2-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
      Term⇓ (substTyp1-substTyp-weakenTyp-inv t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (substTyp1-substTyp-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (weakenTyp-weakenTyp-substTyp1-substTyp-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp-inv t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (substTyp2-substTyp1-substTyp-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (weakenTyp-substTyp2-substTyp1-substTyp-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
      Term⇓ (weakenTyp2-weakenTyp1 t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (weakenTyp1-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (weakenTyp1-weakenTyp-inv t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (weakenTyp1-weakenTyp1-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (substTyp1-weakenTyp1 t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (weakenTyp1-substTyp-weakenTyp1-inv t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (weakenTyp1-substTyp-weakenTyp1 t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (weakenTyp-substTyp-substTyp-weakenTyp1 t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (weakenTyp-substTyp-substTyp-weakenTyp1-inv t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (substTyp-weakenTyp1-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (substTyp3-substTyp2-substTyp1-substTyp-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp1 t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (substTyp1-substTyp-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
      Term⇓ (substTyp2-substTyp-substTyp-weakenTyp1-weakenTyp-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (substTyp1-substTyp-weakenTyp2-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (weakenTyp-weakenTyp1-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ (beta-under-subst t) Γ⇓ = Term⇓ t Γ⇓
      Term⇓ ‘proj₁'’ Γ⇓ (x , p) = x
      Term⇓ ‘proj₂'’ (Γ⇓ , (x , p)) = p
      Term⇓ (‘existT’ x p) Γ⇓ = Term⇓ x Γ⇓ , Term⇓ p Γ⇓
      Term⇓ (f ‘‘’’ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘’ lower (Term⇓ x Γ⇓))
      Term⇓ (f w‘‘’’ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘’ lower (Term⇓ x Γ⇓))
      Term⇓ (f ‘‘→'’’ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘→'’ lower (Term⇓ x Γ⇓))
      Term⇓ (f w‘‘→'’’ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘→'’ lower (Term⇓ x Γ⇓))
      Term⇓ (w→ x) Γ⇓ A⇓ = Term⇓ x (Σ.proj₁ Γ⇓) A⇓
      Term⇓ w‘‘→'’’→‘‘→'’’ Γ⇓ T⇓ = T⇓
      Term⇓ ‘‘→'’’→w‘‘→'’’ Γ⇓ T⇓ = T⇓
      Term⇓ ‘tApp-nd’ Γ⇓ f⇓ x⇓ = lift (SW (lower f⇓ ‘’ₐ lower x⇓))
      Term⇓ ⌜←'⌝ Γ⇓ T⇓ = T⇓
      Term⇓ ⌜→'⌝ Γ⇓ T⇓ = T⇓
      Term⇓ (‘‘fcomp-nd’’ {A} {B} {C}) Γ⇓ g⇓ f⇓ = lift (_‘∘’_ {ε} (lower g⇓) (lower f⇓))
      Term⇓ (⌜‘’⌝ {B} {A} {b}) Γ⇓ = lift (‘λ∙’ {ε} (‘VAR₀’ {ε} {_‘’_ {ε} A b}))
      Term⇓ (⌜‘’⌝' {B} {A} {b}) Γ⇓ = lift (‘λ∙’ {ε} (‘VAR₀’ {ε} {_‘’_ {ε} A b}))
      Term⇓ (‘cast-refl’ {T}) Γ⇓ = lift (cast-proof {T})
      Term⇓ (‘cast-refl'’ {T}) Γ⇓ = lift (cast'-proof {T})
      Term⇓ (‘s→→’ {T} {B} {b} {c} {v}) Γ⇓ = lift (‘idfun’ {_‘’_ {ε} (lower (Term⇓ b tt (Term⇓ v Γ⇓))) (lower (Term⇓ c tt (Term⇓ v Γ⇓)))})
      Term⇓ (‘s←←’ {T} {B} {b} {c} {v}) Γ⇓ = lift (‘idfun’ {_‘’_ {ε} (lower (Term⇓ b tt (Term⇓ v Γ⇓))) (lower (Term⇓ c tt (Term⇓ v Γ⇓)))})
\end{code}

\begin{code}
 module well-typed-syntax-interpreter where
  open well-typed-syntax
  open well-typed-syntax-eq-dec

  max-level : Level
  max-level = well-typed-syntax-pre-interpreter.max-level

  Context⇓ : (Γ : Context) → Set (lsuc max-level)
  Context⇓ = well-typed-syntax-pre-interpreter.inner.Context⇓
             (λ ℓ P Γ' dummy val → context-pick-if {P = P} dummy val)
             (λ ℓ P dummy val → context-pick-if-refl {P = P} {dummy})

  Typ⇓ : {Γ : Context} → Typ Γ → Context⇓ Γ → Set max-level
  Typ⇓ = well-typed-syntax-pre-interpreter.inner.Typ⇓
         (λ ℓ P Γ' dummy val → context-pick-if {P = P} dummy val)
         (λ ℓ P dummy val → context-pick-if-refl {P = P} {dummy})

  Term⇓ : ∀ {Γ : Context} {T : Typ Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Typ⇓ T Γ⇓
  Term⇓ = well-typed-syntax-pre-interpreter.inner.Term⇓
          (λ ℓ P Γ' dummy val → context-pick-if {P = P} dummy val)
          (λ ℓ P dummy val → context-pick-if-refl {P = P} {dummy})

\end{code}

\begin{code}
 module well-typed-syntax-interpreter-full where
  open well-typed-syntax
  open well-typed-syntax-interpreter

  Contextε⇓ : Context⇓ ε
  Contextε⇓ = tt

  Typε⇓ : Typ ε → Set max-level
  Typε⇓ T = Typ⇓ T Contextε⇓

  Termε⇓ : {T : Typ ε} → Term T → Typε⇓ T
  Termε⇓ t = Term⇓ t Contextε⇓

  Typε▻⇓ : ∀ {A} → Typ (ε ▻ A) → Typε⇓ A → Set max-level
  Typε▻⇓ T A⇓ = Typ⇓ T (Contextε⇓ , A⇓)

  Termε▻⇓ : ∀ {A} → {T : Typ (ε ▻ A)} → Term T → (x : Typε⇓ A) → Typε▻⇓ T x
  Termε▻⇓ t x = Term⇓ t (Contextε⇓ , x)

\end{code}

\begin{code}
 module lӧb where
  open well-typed-syntax
  open well-typed-quoted-syntax
  open well-typed-syntax-interpreter-full

  module inner (‘X’ : Typ ε) (‘f’ : Term {Γ = ε ▻ (‘□’ ‘’ ⌜ ‘X’ ⌝T)} (W ‘X’)) where
    X : Set _
    X = Typε⇓ ‘X’

    f'' : (x : Typε⇓ (‘□’ ‘’ ⌜ ‘X’ ⌝T)) → Typε▻⇓ {‘□’ ‘’ ⌜ ‘X’ ⌝T} (W ‘X’) x
    f'' = Termε▻⇓ ‘f’

    dummy : Typ ε
    dummy = ‘Context’

    cast : (Γv : Σ Context Typ) → Typ (ε ▻ ‘Σ’ ‘Context’ ‘Typ’)
    cast (Γ , v) = context-pick-if {P = Typ} {Γ} (W dummy) v

    Hf : (h : Σ Context Typ) → Typ ε
    Hf h = (cast h ‘’ quote-sigma h ‘→'’ ‘X’)

    qh : Term {Γ = (ε ▻ ‘Σ’ ‘Context’ ‘Typ’)} (W (‘Typ’ ‘’ ‘ε’))
    qh = f' w‘‘’’ x
      where
        f' : Term (W (‘Typ’ ‘’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c))
        f' = w→ ‘cast’ ‘'’ₐ ‘VAR₀’

        x : Term (W (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ ⌜ ‘Σ’ ‘Context’ ‘Typ’ ⌝T))
        x = (w→ ‘quote-sigma’ ‘'’ₐ ‘VAR₀’)

    h2 : Typ (ε ▻ ‘Σ’ ‘Context’ ‘Typ’)
    h2 = (W1 ‘□’ ‘’ (qh w‘‘→'’’ w ⌜ ‘X’ ⌝T))

    h : Σ Context Typ
    h = ((ε ▻ ‘Σ’ ‘Context’ ‘Typ’) , h2)

    H0 : Typ ε
    H0 = Hf h

    H : Set
    H = Term {Γ = ε} H0

    ‘H0’ : □ (‘Typ’ ‘’ ⌜ ε ⌝c)
    ‘H0’ = ⌜ H0 ⌝T

    ‘H’ : Typ ε
    ‘H’ = ‘□’ ‘’ ‘H0’

    H0' : Typ ε
    H0' = ‘H’ ‘→'’ ‘X’

    H' : Set
    H' = Term {Γ = ε} H0'

    ‘H0'’ : □ (‘Typ’ ‘’ ⌜ ε ⌝c)
    ‘H0'’ = ⌜ H0' ⌝T

    ‘H'’ : Typ ε
    ‘H'’ = ‘□’ ‘’ ‘H0'’

    toH-helper-helper : ∀ {k} → h2 ≡ k
      → □ (h2 ‘’ quote-sigma h ‘→'’ ‘□’ ‘’ ⌜ h2 ‘’ quote-sigma h ‘→'’ ‘X’ ⌝T)
      → □ (k ‘’ quote-sigma h ‘→'’ ‘□’ ‘’ ⌜ k ‘’ quote-sigma h ‘→'’ ‘X’ ⌝T)
    toH-helper-helper p x = transport (λ k → □ (k ‘’ quote-sigma h ‘→'’ ‘□’ ‘’ ⌜ k ‘’ quote-sigma h ‘→'’ ‘X’ ⌝T)) p x

    toH-helper : □ (cast h ‘’ quote-sigma h ‘→'’ ‘H’)
    toH-helper = toH-helper-helper
      {k = context-pick-if {P = Typ} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} (W dummy) h2}
      (sym (context-pick-if-refl {P = Typ} {W dummy} {h2}))
      (S₀₀W1'→ ((‘‘→'’’→w‘‘→'’’ ‘∘’ ‘‘fcomp-nd’’ ‘'’ₐ (‘s←←’ ‘‘∘’’ ‘cast-refl’ ‘‘∘’’ ⌜→'⌝ ‘'’ₐ ⌜ ‘λ∙’ ‘VAR₀’ ⌝t)) ‘∘’ ⌜←'⌝))

    ‘toH’ : □ (‘H'’ ‘→'’ ‘H’)
    ‘toH’ = ⌜→'⌝ ‘∘’ ‘‘fcomp-nd’’ ‘'’ₐ (⌜→'⌝ ‘'’ₐ ⌜ toH-helper ⌝t) ‘∘’ ⌜←'⌝

    toH : H' → H
    toH h' = toH-helper ‘∘’ h'

    fromH-helper-helper : ∀ {k} → h2 ≡ k
      → □ (‘□’ ‘’ ⌜ h2 ‘’ quote-sigma h ‘→'’ ‘X’ ⌝T ‘→'’ h2 ‘’ quote-sigma h)
      → □ (‘□’ ‘’ ⌜ k ‘’ quote-sigma h ‘→'’ ‘X’ ⌝T ‘→'’ k ‘’ quote-sigma h)
    fromH-helper-helper p x = transport (λ k → □ (‘□’ ‘’ ⌜ k ‘’ quote-sigma h ‘→'’ ‘X’ ⌝T ‘→'’ k ‘’ quote-sigma h)) p x

    fromH-helper : □ (‘H’ ‘→'’ cast h ‘’ quote-sigma h)
    fromH-helper = fromH-helper-helper
      {k = context-pick-if {P = Typ} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} (W dummy) h2}
      (sym (context-pick-if-refl {P = Typ} {W dummy} {h2}))
      (S₀₀W1'← (⌜→'⌝ ‘∘’ ‘‘fcomp-nd’’ ‘'’ₐ (⌜→'⌝ ‘'’ₐ ⌜ ‘λ∙’ ‘VAR₀’ ⌝t ‘‘∘’’ ‘cast-refl'’ ‘‘∘’’ ‘s→→’) ‘∘’ w‘‘→'’’→‘‘→'’’))

    ‘fromH’ : □ (‘H’ ‘→'’ ‘H'’)
    ‘fromH’ = ⌜→'⌝ ‘∘’ ‘‘fcomp-nd’’ ‘'’ₐ (⌜→'⌝ ‘'’ₐ ⌜ fromH-helper ⌝t) ‘∘’ ⌜←'⌝

    fromH : H → H'
    fromH h' = fromH-helper ‘∘’ h'

    lob : □ ‘X’
    lob = fromH h' ‘'’ₐ ⌜ h' ⌝t
      where
        f' : Term {ε ▻ ‘□’ ‘’ ‘H0’} (W (‘□’ ‘’ (⌜ ‘□’ ‘’ ‘H0’ ⌝T ‘‘→'’’ ⌜ ‘X’ ⌝T)))
        f' = Conv0 {‘H0’} {‘X’} (SW1W (w∀ ‘fromH’ ‘’ₐ ‘VAR₀’))

        x : Term {ε ▻ ‘□’ ‘’ ‘H0’} (W (‘□’ ‘’ ⌜ ‘H’ ⌝T))
        x = w→ ‘quote-term’ ‘'’ₐ ‘VAR₀’

        h' : H
        h' = toH (‘λ∙’ (w→ (‘λ∙’ ‘f’) ‘'’ₐ (w→→ ‘tApp-nd’ ‘'’ₐ f' ‘'’ₐ x)))

  lob : {‘X’ : Typ ε} → □ ((‘□’ ‘’ ⌜ ‘X’ ⌝T) ‘→'’ ‘X’) → □ ‘X’
  lob {‘X’} ‘f’ = inner.lob ‘X’ (un‘λ∙’ ‘f’)

\end{code}
