import Definitions.Def_LanglandsTunnell_JLConverse
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_integrable_dualThetaFree_integrand

set_option autoImplicit false

open MeasureTheory Set LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.integrable_dualThetaFree_integrand
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℝ) (ha : a ≠ 0)
    (β γ : ℂ) (m n : ℕ) (S : ℝ → ℂ) (hSm : Measurable S) (CS : ℝ) (hSb : ∀ y : ℝ, ‖S y‖ ≤ CS)
    (a₁ : ℝ) (ha₁ : a₁ ≠ 0) (a₂ : ℝ) (ha₂ : 0 < a₂) :
    Integrable (fun q : ℝ × ℝ × ℝ =>
        ((q.2.1⁻¹ : ℝ) : ℂ) ^ n * S q.2.1 * ((|q.2.1| : ℝ) : ℂ) ^ β * ((q.2.2 : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * (q.1 ^ 2 / (a₂ * q.2.1) ^ 2))) : ℂ) * ArchR.psi (a * q.1) *
          ((((a₁ * q.2.2 - (a₂ * q.2.2)⁻¹ : ℝ) : ℂ)) + Complex.I * (((q.1 / (a₂ * q.2.1) : ℝ) : ℂ))) ^ m *
          (Real.exp (-(Real.pi * (((a₂ * q.2.2) ^ 2)⁻¹ + (q.2.1 ^ 2)⁻¹ + a₁ ^ 2 * q.2.2 ^ 2))) : ℂ) *
          D.W (ArchR.diagOne (a * (q.2.1 / q.2.2))))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_integrable_dualThetaFree_integrand.solution
