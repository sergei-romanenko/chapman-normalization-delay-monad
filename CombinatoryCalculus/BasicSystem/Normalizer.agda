module BasicSystem.Normalizer where

open import BasicSystem.DelayMonad
open import BasicSystem.Utils
open import BasicSystem.Syntax


--
-- Normalization by evaluation with the delay monad.
--

infixl 5 _⟨∙⟩_

mutual

  _⟨∙⟩_ : ∀ {α β i} (u : Nf (α ⇒ β)) (v : Nf α) → Delay i (Nf β)

  K0 ⟨∙⟩ u = now (K1 u)
  K1 u ⟨∙⟩ v = now u
  S0 ⟨∙⟩ u = now (S1 u)
  S1 u ⟨∙⟩ v = now (S2 u v)
  S2 u v ⟨∙⟩ w = later (∞S u v w)

  ∞S : ∀ {α β γ i}
    (u : Nf (α ⇒ β ⇒ γ)) (v : Nf (α ⇒ β)) (w : Nf α) → ∞Delay i (Nf γ)
  force (∞S u v w) {j} =
    u ⟨∙⟩ w >>= λ uw → v ⟨∙⟩ w >>= λ vw → uw ⟨∙⟩ vw

  ⟦_⟧ : ∀ {α i} (x : Tm α) → Delay i (Nf α)

  ⟦ K ⟧ = now K0
  ⟦ S ⟧ = now S0
  ⟦ x ∙ y ⟧ =
    ⟦ x ⟧ >>= λ u → ⟦ y ⟧ >>= λ v → u ⟨∙⟩ v

-- Normalizer

norm? : ∀ {α} (x : Tm α) → ∀ {i} → Delay i (Tm α)
norm? x = ⌜_⌝ <$> ⟦ x ⟧
