import Mathlib
import P2M.Util
import P2M.Sol.S_Subring_eq_of_isMaximal_of_marked_galois_descent
set_option autoImplicit false

theorem Subring.eq_of_isMaximal_of_marked_galois_descent
    {Ω : Type*} [Field Ω] (R₀ : Subring Ω) (F₀ Λ : Subfield Ω) (φ : Ω →+* Ω)
    (hRF : R₀ ≤ F₀.toSubring)
    (hfrac : ∀ x ∈ F₀, ∃ y z : Ω, y ∈ R₀ ∧ z ∈ R₀ ∧ z ≠ 0 ∧ x * z = y)
    (hFL : ∀ x ∈ F₀, φ x ∈ Λ)
    (S : Set Ω) (hS : S.Finite) (hSL : S ⊆ Λ) (hSint : ∀ s ∈ S, (φ.comp R₀.subtype).IsIntegralElem s)
    (hgen : Λ ≤ Subfield.closure ((F₀.map φ : Set Ω) ∪ S))
    (T : Subring Ω) (hTL : T ≤ Λ.toSubring) (hTS : T ≤ Subring.closure ((R₀.map φ : Set Ω) ∪ S))
    {ι : Type*} (G : ι → Set Ω) (hGT : ∀ i, G i ⊆ T)
    (cov : ∀ (B' : Subring Ω) (hBL : B' ≤ Λ.toSubring) (_hRB : ∀ x ∈ R₀, φ x ∈ B') (hTB : T ≤ B')
      (_hint : ∀ x ∈ B', (φ.comp R₀.subtype).IsIntegralElem x) (N : Ideal ↥B'), N.IsMaximal →
      ∃ i, ∀ (g : Ω) (hg : g ∈ G i), (⟨g, hTB (hGT i hg)⟩ : ↥B') ∈ N)
    (uniq : ∀ (i : ι) (B' : Subring Ω) (hBL : B' ≤ Λ.toSubring) (_hRB : ∀ x ∈ R₀, φ x ∈ B') (hTB : T ≤ B')
      (_hint : ∀ x ∈ B', (φ.comp R₀.subtype).IsIntegralElem x) (P₁ P₂ : Ideal ↥B'), P₁.IsPrime → P₂.IsPrime →
      (∀ (g : Ω) (hg : g ∈ G i), (⟨g, hTB (hGT i hg)⟩ : ↥B') ∈ P₁) →
      (∀ (g : Ω) (hg : g ∈ G i), (⟨g, hTB (hGT i hg)⟩ : ↥B') ∈ P₂) → P₁ = P₂)
    (trans : ∀ i j : ι, ∃ σ : ↥Λ ≃+* ↥Λ,
      (∀ x : ↥Λ, (x : Ω) ∈ F₀.map φ → σ x = x) ∧
      ∀ (B' : Subring Ω) (hBL : B' ≤ Λ.toSubring) (hTB : T ≤ B')
        (hσB : ∀ (b : Ω) (hb : b ∈ B'), ((σ ⟨b, hBL hb⟩ : ↥Λ) : Ω) ∈ B') (I : Ideal ↥B'),
        (∀ (g : Ω) (hg : g ∈ G i), (⟨g, hTB (hGT i hg)⟩ : ↥B') ∈ I) →
        ∀ (g : Ω) (hg : g ∈ G j), (⟨((σ ⟨g, hBL (hTB (hGT j hg))⟩ : ↥Λ) : Ω), hσB _ (hTB (hGT j hg))⟩ : ↥B') ∈ I)
    (B : Subring Ω) (hRB : R₀ ≤ B) (hBF : B ≤ F₀.toSubring) (hBint : ∀ x ∈ B, IsIntegral ↥R₀ x)
    (P₁ P₂ : Ideal ↥B) [P₁.IsMaximal] [P₂.IsMaximal] :
    P₁ = P₂ := by p2m_exact_reverting @_root_.P2MW.S_Subring_eq_of_isMaximal_of_marked_galois_descent.solution
