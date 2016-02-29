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
       W₁ : ∀ {Γ A B} → Type (Γ ▻ B) → Type (Γ ▻ A ▻ (W {Γ = Γ} {A = A} B))
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
       ⌜_⌝ᵗ : ∀ {Γ T} → Term {Γ} T → Term {Γ} (‘Term’ ‘’ ⌜ T ⌝)
       ‘⌜‘VAR₀’⌝ᵗ’ : ∀ {Γ T} → Term {Γ ▻ ‘Term’ ‘’ ⌜ T ⌝} (W (‘Term’ ‘’ ⌜ ‘Term’ ‘’ ⌜ T ⌝ ⌝))
       ‘⌜‘VAR₀’⌝’ : ∀ {Γ} → Term {Γ ▻ ‘Type’ Γ} (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝))
       ‘λ’ : ∀ {Γ A B} → Term {Γ ▻ A} (W B) → Term {Γ} (A ‘→’ B)
       ‘VAR₀’ : ∀ {Γ T} → Term {Γ ▻ T} (W T)
       _‘’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
       ‘‘×'’’ : ∀ {Γ} → Term {Γ} (‘Type’ Γ ‘→’ ‘Type’ Γ ‘→’ ‘Type’ Γ)
       quine→ : ∀ {Γ φ} → Term {Γ} (Quine φ        ‘→’ φ ‘’ ⌜ Quine φ ⌝)
       quine← : ∀ {Γ φ} → Term {Γ} (φ ‘’ ⌜ Quine φ ⌝ ‘→’ Quine φ)
       ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
       SW : ∀ {Γ X A} {a : Term A} → Term {Γ} (W X ‘’ a) → Term X
       →SW₁SV→W : ∀ {Γ T X A B} {x : Term X}
         → Term {Γ} (T ‘→’ (W₁ A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x)
         → Term {Γ} (T ‘→’ A ‘’ x ‘→’ B)
       ←SW₁SV→W : ∀ {Γ T X A B} {x : Term X}
         → Term {Γ} ((W₁ A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x ‘→’ T)
         → Term {Γ} ((A ‘’ x ‘→’ B) ‘→’ T)
       →SW₁SV→SW₁SV→W : ∀ {Γ T X A B} {x : Term X}
         → Term {Γ} (T ‘→’ (W₁ A ‘’ ‘VAR₀’ ‘→’ W₁ A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x)
         → Term {Γ} (T ‘→’ A ‘’ x ‘→’ A ‘’ x ‘→’ B)
       ←SW₁SV→SW₁SV→W : ∀ {Γ T X A B} {x : Term X}
         → Term {Γ} ((W₁ A ‘’ ‘VAR₀’ ‘→’ W₁ A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x ‘→’ T)
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
     ⟦_⟧ᶜ : (Γ : Context) → Set (lsuc max-level)
     ⟦ ε ⟧ᶜ = ⊤
     ⟦ Γ ▻ T ⟧ᶜ = Σ ⟦ Γ ⟧ᶜ ⟦ T ⟧ᵀ

     ⟦_⟧ᵀ : {Γ : Context} → Type Γ → ⟦ Γ ⟧ᶜ → Set max-level
     ⟦_⟧ᵀ (W T) ⟦Γ⟧ = ⟦ T ⟧ᵀ (Σ.proj₁ ⟦Γ⟧)
     ⟦_⟧ᵀ (W₁ T) ⟦Γ⟧ = ⟦ T ⟧ᵀ ((Σ.proj₁ (Σ.proj₁ ⟦Γ⟧)) , (Σ.proj₂ ⟦Γ⟧))
     ⟦_⟧ᵀ (T ‘’ x) ⟦Γ⟧ = ⟦ T ⟧ᵀ (⟦Γ⟧ , ⟦ x ⟧ᵗ ⟦Γ⟧)
     ⟦_⟧ᵀ (‘Type’ Γ) ⟦Γ⟧ = Lifted (Type Γ)
     ⟦_⟧ᵀ ‘Term’ ⟦Γ⟧ = Lifted (Term (lower (Σ.proj₂ ⟦Γ⟧)))
     ⟦_⟧ᵀ (A ‘→’ B) ⟦Γ⟧ = ⟦ A ⟧ᵀ ⟦Γ⟧ → ⟦ B ⟧ᵀ ⟦Γ⟧
     ⟦_⟧ᵀ (A ‘×’ B) ⟦Γ⟧ = ⟦ A ⟧ᵀ ⟦Γ⟧ × ⟦ B ⟧ᵀ ⟦Γ⟧
     ⟦ ‘⊤’ ⟧ᵀ ⟦Γ⟧ = ⊤
     ⟦ ‘⊥’ ⟧ᵀ ⟦Γ⟧ = ⊥
     ⟦_⟧ᵀ (Quine φ) ⟦Γ⟧ = ⟦ φ ⟧ᵀ (⟦Γ⟧ , (lift (Quine φ)))

     ⟦_⟧ᵗ : ∀ {Γ : Context} {T : Type Γ} → Term T → (⟦Γ⟧ : ⟦ Γ ⟧ᶜ) → ⟦ T ⟧ᵀ ⟦Γ⟧
     ⟦_⟧ᵗ ⌜ x ⌝ ⟦Γ⟧ = lift x
     ⟦_⟧ᵗ ⌜ x ⌝ᵗ ⟦Γ⟧ = lift x
     ⟦_⟧ᵗ ‘⌜‘VAR₀’⌝ᵗ’ ⟦Γ⟧ = lift ⌜ (lower (Σ.proj₂ ⟦Γ⟧)) ⌝ᵗ
     ⟦_⟧ᵗ ‘⌜‘VAR₀’⌝’ ⟦Γ⟧ = lift ⌜ (lower (Σ.proj₂ ⟦Γ⟧)) ⌝
     ⟦_⟧ᵗ (f ‘’ₐ x) ⟦Γ⟧ = ⟦ f ⟧ᵗ ⟦Γ⟧ (⟦ x ⟧ᵗ ⟦Γ⟧)
     ⟦_⟧ᵗ ‘tt’ ⟦Γ⟧ = tt
     ⟦_⟧ᵗ (quine→ {φ}) ⟦Γ⟧ x = x
     ⟦_⟧ᵗ (quine← {φ}) ⟦Γ⟧ x = x
     ⟦_⟧ᵗ (‘λ’ f) ⟦Γ⟧ x = ⟦ f ⟧ᵗ (⟦Γ⟧ , x)
     ⟦_⟧ᵗ ‘VAR₀’ ⟦Γ⟧ = Σ.proj₂ ⟦Γ⟧
     ⟦_⟧ᵗ (SW t) = ⟦_⟧ᵗ t
     ⟦_⟧ᵗ (←SW₁SV→W f) = ⟦ f ⟧ᵗ
     ⟦_⟧ᵗ (→SW₁SV→W f) = ⟦ f ⟧ᵗ
     ⟦_⟧ᵗ (←SW₁SV→SW₁SV→W f) = ⟦ f ⟧ᵗ
     ⟦_⟧ᵗ (→SW₁SV→SW₁SV→W f) = ⟦ f ⟧ᵗ
     ⟦_⟧ᵗ (w x) ⟦Γ⟧ = ⟦ x ⟧ᵗ (Σ.proj₁ ⟦Γ⟧)
     ⟦_⟧ᵗ (w→ f) ⟦Γ⟧ = ⟦ f ⟧ᵗ ⟦Γ⟧
     ⟦_⟧ᵗ (→w f) ⟦Γ⟧ = ⟦ f ⟧ᵗ ⟦Γ⟧
     ⟦_⟧ᵗ (ww→ f) ⟦Γ⟧ = ⟦ f ⟧ᵗ ⟦Γ⟧
     ⟦_⟧ᵗ (→ww f) ⟦Γ⟧ = ⟦ f ⟧ᵗ ⟦Γ⟧
     ⟦_⟧ᵗ ‘‘×'’’ ⟦Γ⟧ A B = lift (lower A ‘×’ lower B)
     ⟦_⟧ᵗ (g ‘∘’ f) ⟦Γ⟧ x = ⟦ g ⟧ᵗ ⟦Γ⟧ (⟦ f ⟧ᵗ ⟦Γ⟧ x)
     ⟦_⟧ᵗ (f w‘‘’’ₐ x) ⟦Γ⟧ = lift (lower (⟦ f ⟧ᵗ ⟦Γ⟧) ‘’ₐ lower (⟦ x ⟧ᵗ ⟦Γ⟧))
     ⟦_⟧ᵗ ‘‘’ₐ’ ⟦Γ⟧ f x = lift (lower f ‘’ₐ lower x)
     ⟦_⟧ᵗ (‘‘□’’ {Γ} T) ⟦Γ⟧ = lift (‘Term’ ‘’ lower (⟦_⟧ᵗ T ⟦Γ⟧))
     ⟦_⟧ᵗ (A ‘‘→’’ B) ⟦Γ⟧ = lift ((lower (⟦_⟧ᵗ A ⟦Γ⟧)) ‘→’ (lower (⟦_⟧ᵗ B ⟦Γ⟧)))
     ⟦_⟧ᵗ (A ww‘‘‘→’’’ B) ⟦Γ⟧ = lift ((lower (⟦_⟧ᵗ A ⟦Γ⟧)) ‘‘→’’ (lower (⟦_⟧ᵗ B ⟦Γ⟧)))
     ⟦_⟧ᵗ (A ww‘‘‘×’’’ B) ⟦Γ⟧ = lift ((lower (⟦_⟧ᵗ A ⟦Γ⟧)) ‘‘×’’ (lower (⟦_⟧ᵗ B ⟦Γ⟧)))


   module inner (‘X’ : Type ε) (‘f’ : Term {ε} (‘□’ ‘X’ ‘→’ ‘X’)) where
     ‘H’ : Type ε
     ‘H’ = Quine (W₁ ‘Term’ ‘’ ‘VAR₀’ ‘→’ W ‘X’)

     ‘toH’ : □ ((‘□’ ‘H’ ‘→’ ‘X’) ‘→’ ‘H’)
     ‘toH’ = ←SW₁SV→W quine←

     ‘fromH’ : □ (‘H’ ‘→’ (‘□’ ‘H’ ‘→’ ‘X’))
     ‘fromH’ = →SW₁SV→W quine→

     ‘□‘H’→□‘X’’ : □ (‘□’ ‘H’ ‘→’ ‘□’ ‘X’)
     ‘□‘H’→□‘X’’ = ‘λ’ (w ⌜ ‘fromH’ ⌝ᵗ w‘‘’’ₐ ‘VAR₀’ w‘‘’’ₐ ‘⌜‘VAR₀’⌝ᵗ’)

     ‘h’ : Term ‘H’
     ‘h’ = ‘toH’ ‘’ₐ (‘f’ ‘∘’ ‘□‘H’→□‘X’’)

     Lӧb : □ ‘X’
     Lӧb = ‘fromH’ ‘’ₐ ‘h’ ‘’ₐ ⌜ ‘h’ ⌝ᵗ

   Lӧb : ∀ {X} → Term {ε} (‘□’ X ‘→’ X) → Term {ε} X
   Lӧb {X} f = inner.Lӧb X f

   ⟦_⟧ : Type ε → Set _
   ⟦ T ⟧ = ⟦ T ⟧ᵀ tt

   ‘¬’_ : ∀ {Γ} → Type Γ → Type Γ
   ‘¬’ T = T ‘→’ ‘⊥’

   _w‘‘×’’_ : ∀ {Γ X} → Term {Γ ▻ X} (W (‘Type’ Γ)) → Term {Γ ▻ X} (W (‘Type’ Γ)) → Term {Γ ▻ X} (W (‘Type’ Γ))
   A w‘‘×’’ B = w→ (w→ (w ‘‘×'’’) ‘’ₐ A) ‘’ₐ B

   lӧb : ∀ {‘X’} → □ (‘□’ ‘X’ ‘→’ ‘X’) → ⟦ ‘X’ ⟧
   lӧb f = ⟦_⟧ᵗ (Lӧb f) tt

   ¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
   ¬_ {ℓ} T = T → ⊥ {ℓ}

   incompleteness : ¬ □ (‘¬’ (‘□’ ‘⊥’))
   incompleteness = lӧb

   soundness : ¬ □ ‘⊥’
   soundness x = ⟦ x ⟧ᵗ tt

   non-emptyness : Σ (Type ε) (λ T → □ T)
   non-emptyness = ‘⊤’ , ‘tt’
\end{code}
