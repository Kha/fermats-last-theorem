import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_one_sub_normSq_add_normSq_conj_add_conj_mul_eq_add_abs_mul_of_hasCompactSupport

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_contDiff_integral_integral_mul_log_sq_one_sub_normSq_add_normSq_conj_add_conj_mul_eq_add_abs_mul_of_hasCompactSupport
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (g : P × (ℂ × V) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (ϱ : P → ℂ) (hϱ : ContDiff ℝ (⊤ : ℕ∞) ϱ) :
    ∃ A B : P → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ p : P,
        Integrable (fun zv : ℂ × V =>
          g (p, zv) * (Real.log ((1 - ‖ϱ p‖ ^ 2) ^ 2 +
            ‖(starRingEnd ℂ) zv.1 + (starRingEnd ℂ) (ϱ p) * zv.1‖ ^ 2) : ℂ)) ((volume : Measure ℂ).prod μ) ∧
        ∫ zv : ℂ × V, g (p, zv) * (Real.log ((1 - ‖ϱ p‖ ^ 2) ^ 2 +
            ‖(starRingEnd ℂ) zv.1 + (starRingEnd ℂ) (ϱ p) * zv.1‖ ^ 2) : ℂ) ∂((volume : Measure ℂ).prod μ) =
          A p + ((|1 - ‖ϱ p‖ ^ 2| : ℝ) : ℂ) * B p := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_one_sub_normSq_add_normSq_conj_add_conj_mul_eq_add_abs_mul_of_hasCompactSupport.solution
