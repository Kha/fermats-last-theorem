import Mathlib
import P2M.Util
import P2M.Sol.S_ContinuousLinearMap_exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass

set_option autoImplicit false

open MeasureTheory

theorem ContinuousLinearMap.exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass
    (d : ℕ) (XK : Set (Fin d → ℂ × ℂ))
    (emb : C((Fin d → AddCircle (1 : ℝ)), XK))
    (hemb : ∀ (θ : Fin d → AddCircle (1 : ℝ)) (i : Fin d),
      ((emb θ : XK) : Fin d → ℂ × ℂ) i = ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ)))
    (μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ)
    (hμ : ∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) :
    ∃ Λ : C(XK, ℂ) →L[ℂ] ℂ,
      (∀ h : C(XK, ℂ), Λ h = μ (h.comp emb)) ∧
      ∀ (τ : Fin d → ℂ × ℂ), ∀ ε > (0 : ℝ), ∃ U : Fin d → Set (ℂ × ℂ),
        (∀ v ∈ (Finset.univ : Finset (Fin d)), IsOpen (U v) ∧ τ v ∈ U v) ∧
        ∀ g : C(XK, ℂ), (∀ y : XK, (∃ v ∈ (Finset.univ : Finset (Fin d)), (y : Fin d → ℂ × ℂ) v ∉ U v) → g y = 0) →
          (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε := by p2m_exact_reverting @_root_.P2MW.S_ContinuousLinearMap_exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass.solution
