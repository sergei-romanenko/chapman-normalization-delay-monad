module BasicSystem.StrongComp where

open import BasicSystem.Utils
open import BasicSystem.DelayMonad
open import BasicSystem.Syntax
open import BasicSystem.Normalizer

--
-- "Strong computability" of normal forms.
--

SC : ∀ {α} (u : Nf α) → Set
SC {⋆} u = ⊤
SC {α ⇒ β} u = ∀ (v : Nf α) (q : SC v) →
    ∃ λ w → SC w × (u ⟨∙⟩ v ⇓ w) × ⌜ u ⌝ ∙ ⌜ v ⌝ ≈ ⌜ w ⌝

-- ∀ {α} (x : Tm α) → ∃ λ u → SC u × ⟦ x ⟧ ⇓ u

mutual

  all-sc-K1 : ∀ {α β} (u : Nf α) (p : SC u) → SC (K1 {α} {β} u)
  all-sc-K1 u p v q = u , p , now⇓ , ≈K

  all-sc-K0 : ∀ {α β} → SC (K0 {α} {β})
  all-sc-K0 u p = K1 u , all-sc-K1 u p , now⇓ , ≈refl

  all-sc-S2 : ∀ {α β γ} u (p : SC u) v (q : SC v) →
    SC (S2 {α} {β} {γ} u v)
  all-sc-S2 u p v q w r
    with p w r | q w r
  ... | uw , pr , ⇓uw , ≈uw | vw , qr , ⇓vw , ≈vw
    with pr vw qr
  ... | uwvw , prqr , ⇓uwvw , ≈uwvw
    = uwvw , prqr , later⇓ >>=⇓uwvw , suvw≈uwvw
    where
    open ≈-Reasoning
    >>=⇓uwvw : (u ⟨∙⟩ w >>= λ uw → v ⟨∙⟩ w >>= _⟨∙⟩_ uw) ⇓ uwvw
    >>=⇓uwvw = bind2⇓ _⟨∙⟩_ ⇓uw ⇓vw (uw ⟨∙⟩ vw ⇓ uwvw ∋ ⇓uwvw)
    suvw≈uwvw : S ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ ⌜ w ⌝ ≈ ⌜ uwvw ⌝
    suvw≈uwvw = begin
      S ∙ ⌜ u ⌝ ∙ ⌜ v ⌝ ∙ ⌜ w ⌝
        ≈⟨ ≈S ⟩
      (⌜ u ⌝ ∙ ⌜ w ⌝) ∙ (⌜ v ⌝ ∙ ⌜ w ⌝)
        ≈⟨ ≈cong∙ ≈uw ≈vw ⟩
      ⌜ uw ⌝ ∙ ⌜ vw ⌝
        ≈⟨ ≈uwvw ⟩
      ⌜ uwvw ⌝
      ∎

  all-sc-S1 : ∀ {α β γ} u (p : SC u) →
    SC (S1 {α} {β} {γ} u)
  all-sc-S1 u p v q = S2 u v , all-sc-S2 u p v q , now⇓ , ≈refl

  all-sc-S0 : ∀ {α β γ} → SC (S0 {α} {β} {γ})
  all-sc-S0 u p = S1 u , all-sc-S1 u p , now⇓ , ≈refl

  -- (x : Tm α) → ∃ λ u → SC u × ⟦ x ⟧ ⇓ u

  all-sc : ∀ {α} (x : Tm α) → ∃ λ u → SC u × ⟦ x ⟧ ⇓ u
  all-sc K = K0 , all-sc-K0 , now⇓
  all-sc S = S0 , all-sc-S0 , now⇓
  all-sc (x ∙ y)
    with all-sc x | all-sc y
  ... | u , p , ⇓u | v , q , ⇓v
    with p v q
  ... | uv , pq , ⇓uv , ≈uv
    = uv , pq , >>=⇓uv
    where
    >>=⇓uv : (⟦ x ⟧ >>= λ u → ⟦ y ⟧ >>= λ v → u ⟨∙⟩ v) ⇓ uv
    >>=⇓uv = bind2⇓ _⟨∙⟩_ ⇓u ⇓v (u ⟨∙⟩ v ⇓ uv ∋ ⇓uv)
--
-- Normalizer.
--

nf : ∀ {α} (x : Tm α) → Nf α
nf x
  with all-sc x
... | u , ⇓u , p
  = u

norm : ∀ {α} (x : Tm α) → Tm α
norm = ⌜_⌝ ∘ nf
