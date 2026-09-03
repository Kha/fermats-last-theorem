import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_contDiff_integral_integral_mul_log_normSq_clm_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_contDiff_integral_integral_mul_log_normSq_clm_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (g : P × (ℂ × V) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (L : P → (ℂ →L[ℝ] ℂ)) (hL : ContDiff ℝ (⊤ : ℕ∞) L) (hL0 : ∀ (p : P) (z : ℂ), L p z = 0 → z = 0)
    (φ : P → (V →L[ℝ] ℂ)) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∃ A B : P × ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (p : P) (r : ℂ),
        Integrable (fun zv : ℂ × V =>
          g (p, zv) * (Real.log (‖L p zv.1 + φ p zv.2‖ ^ 2 + ‖r‖ ^ 2) : ℂ)) ((volume : Measure ℂ).prod μ) ∧
        ∫ zv : ℂ × V, g (p, zv) * (Real.log (‖L p zv.1 + φ p zv.2‖ ^ 2 + ‖r‖ ^ 2) : ℂ) ∂((volume : Measure ℂ).prod μ) =
          A (p, r) + ((‖r‖ ^ 2 * Real.log ‖r‖ : ℝ) : ℂ) * B (p, r) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_contDiff_integral_integral_mul_log_normSq_clm_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport.solution
