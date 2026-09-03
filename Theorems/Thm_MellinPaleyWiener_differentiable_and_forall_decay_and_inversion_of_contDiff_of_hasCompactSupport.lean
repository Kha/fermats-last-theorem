import Mathlib
import P2M.Util
import P2M.Sol.S_MellinPaleyWiener_differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport

set_option autoImplicit false

open MeasureTheory

theorem MellinPaleyWiener.differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport
    (h : ℝ → ℂ) (_hh : ContDiff ℝ (⊤ : ℕ∞) h) (_hhc : HasCompactSupport h) :
    Differentiable ℂ (fun s : ℂ => ∫ u : ℝ, h u * Complex.exp (s * (u : ℂ))) ∧
    (∀ (n : ℕ) (σ₀ : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ → ∀ t : ℝ,
      (1 + |t|) ^ n * ‖∫ u : ℝ, h u * Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))‖ ≤ C) ∧
    (∀ (σ' u : ℝ), h u = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ, (∫ v : ℝ, h v * Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (v : ℂ))) *
        Complex.exp (-(((σ' : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)))) := by p2m_exact_reverting @_root_.P2MW.S_MellinPaleyWiener_differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport.solution
