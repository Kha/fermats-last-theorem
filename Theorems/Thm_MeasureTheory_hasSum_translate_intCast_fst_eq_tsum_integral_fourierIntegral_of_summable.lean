import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_hasSum_translate_intCast_fst_eq_tsum_integral_fourierIntegral_of_summable

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.hasSum_translate_intCast_fst_eq_tsum_integral_fourierIntegral_of_summable
    (a b : ℕ) (f : (Fin a → ℝ) × (Fin b → ℝ) → ℂ) (hfc : Continuous f) (hfi : Integrable f)
    (hloc : ∀ y : (Fin a → ℝ) × (Fin b → ℝ), ∃ V ∈ nhds y, ∃ M : (Fin a → ℤ) → ℝ, Summable M ∧
      ∀ y' ∈ V, ∀ k : Fin a → ℤ, ‖f (y' + (fun i => (k i : ℝ), 0))‖ ≤ M k)
    (fhat : (Fin a → ℤ) → (Fin b → ℝ) → ℂ)
    (hfhat : ∀ (κ : Fin a → ℤ) (η : Fin b → ℝ), fhat κ η =
      ∫ p : (Fin a → ℝ) × (Fin b → ℝ),
        Complex.exp (-(2 * Real.pi * Complex.I *
          ((∑ i, (κ i : ℝ) * p.1 i + ∑ j, η j * p.2 j : ℝ) : ℂ))) * f p)
    (hint : ∀ κ : Fin a → ℤ, Integrable (fhat κ))
    (hsum : Summable (fun κ : Fin a → ℤ => ∫ η, ‖fhat κ η‖)) :
    (∀ κ : Fin a → ℤ, Continuous (fhat κ)) ∧
    ∀ y : (Fin a → ℝ) × (Fin b → ℝ),
      Summable (fun k : Fin a → ℤ => ‖f (y + (fun i => (k i : ℝ), 0))‖) ∧
      HasSum (fun k : Fin a → ℤ => f (y + (fun i => (k i : ℝ), 0)))
        (∑' κ : Fin a → ℤ, ∫ η : Fin b → ℝ, fhat κ η *
          Complex.exp (2 * Real.pi * Complex.I *
            ((∑ i, (κ i : ℝ) * y.1 i + ∑ j, η j * y.2 j : ℝ) : ℂ))) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_hasSum_translate_intCast_fst_eq_tsum_integral_fourierIntegral_of_summable.solution
