import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable
    {c : ℕ} (F : (Fin c → ℝ) → ℂ) (hF : Continuous F)
    (hper : ∀ (θ : Fin c → ℝ) (j : Fin c), F (θ + Pi.single j 1) = F θ)
    (hsum : Summable fun m : Fin c → ℤ =>
      ‖∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          F θ * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))‖)
    (θ : Fin c → ℝ) :
    HasSum (fun m : Fin c → ℤ =>
      (∫ θ' in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          F θ' * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ' j : ℝ) : ℂ)))) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))) (F θ) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable.solution
