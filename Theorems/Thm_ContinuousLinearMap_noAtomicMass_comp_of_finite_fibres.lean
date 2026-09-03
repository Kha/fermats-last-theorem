import Mathlib
import P2M.Util
import P2M.Sol.S_ContinuousLinearMap_noAtomicMass_comp_of_finite_fibres

set_option autoImplicit false

theorem ContinuousLinearMap.noAtomicMass_comp_of_finite_fibres
    {ιK ιL : Type} (XK : Set (ιK → ℂ × ℂ)) (hXKc : IsCompact XK) (X : Set (ιL → ℂ × ℂ)) (T : Finset ιK)
    (w' : ιK → ιL)
    (B : ιK → ℂ × ℂ → ℂ × ℂ) (hBc : ∀ v ∈ T, Continuous (B v))
    (hBf : ∀ v ∈ T, ∀ c : ℂ × ℂ, ((B v) ⁻¹' {c}).Finite)
    (bc : C(XK, X))
    (hbc : ∀ (x : XK), ∀ v ∈ T, ((bc x : X) : ιL → ℂ × ℂ) (w' v) = B v ((x : ιK → ℂ × ℂ) v))
    (Λ : C(XK, ℂ) →L[ℂ] ℂ)
    (hΛ : ∀ (τ : ιK → ℂ × ℂ), ∀ ε > (0 : ℝ), ∃ U : ιK → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
      ∀ g : C(XK, ℂ), (∀ y : XK, (∃ v ∈ T, (y : ιK → ℂ × ℂ) v ∉ U v) → g y = 0) → (∀ y, ‖g y‖ ≤ 1) →
        ‖Λ g‖ < ε) :
    ∀ (τ : ιK → ℂ × ℂ), ∀ ε > (0 : ℝ), ∃ U : ιK → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
      ∀ g : C(X, ℂ), (∀ y : X, (∃ v ∈ T, (y : ιL → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) → (∀ y, ‖g y‖ ≤ 1) →
        ‖Λ (g.comp bc)‖ < ε := by p2m_exact_reverting @_root_.P2MW.S_ContinuousLinearMap_noAtomicMass_comp_of_finite_fibres.solution
