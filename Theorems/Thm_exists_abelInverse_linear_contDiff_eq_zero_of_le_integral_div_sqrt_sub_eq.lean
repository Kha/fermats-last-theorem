import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Sqrt
import P2M.Util
import P2M.Sol.S_exists_abelInverse_linear_contDiff_eq_zero_of_le_integral_div_sqrt_sub_eq

set_option autoImplicit false

open MeasureTheory

theorem exists_abelInverse_linear_contDiff_eq_zero_of_le_integral_div_sqrt_sub_eq
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ∃ T : (ℝ → ℂ) → (ℝ → ℂ),
      (∀ f g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
        HasCompactSupport g → ∀ a b : ℂ, T (fun ξ => a * f ξ + b * g ξ) = fun ξ => a * T f ξ + b * T g ξ) ∧
      ∀ G : ℝ × P → ℂ, ContDiff ℝ (⊤ : ℕ∞) G → HasCompactSupport G →
        ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × P => T (fun ξ => G (ξ, q.2)) q.1) ∧
        (∀ R : ℝ, (∀ (p : P) (ξ : ℝ), R ≤ ξ → G (ξ, p) = 0) →
          ∀ (p : P) (ξ : ℝ), R ≤ ξ → T (fun ξ' => G (ξ', p)) ξ = 0) ∧
        ∀ (η : ℝ) (p : P),
          ∫ ξ in Set.Ioi η, T (fun ξ' => G (ξ', p)) ξ / ((Real.sqrt (ξ - η) : ℝ) : ℂ) = G (η, p) := by p2m_exact_reverting @_root_.P2MW.S_exists_abelInverse_linear_contDiff_eq_zero_of_le_integral_div_sqrt_sub_eq.solution
