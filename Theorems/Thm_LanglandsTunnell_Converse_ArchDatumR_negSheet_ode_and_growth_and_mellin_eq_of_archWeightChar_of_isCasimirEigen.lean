import Mathlib
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_ArchDatumR_negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen

set_option autoImplicit false

open Real Complex
open NumberField AutomorphicForm
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.ArchDatumR.negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen
    (P : RealArchParam) (D : ArchDatumR P) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D)
    (ν : ℂ) (hν : P.laplaceEigenvalue = 1 / 4 - ν ^ 2)
    (c₀ : ℂ) (hA : ∀ (a : ZMod 2) (s : ℂ), (P.twist 0 a).archFactor s = Complex.Gammaℂ (s + c₀)) :
    let f : ℝ → ℂ := fun y => D.W !![-Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]
    (DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((-(k₀ : ℝ) : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) ∧
    (∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N) ∧
    (∃ (σ₀ : ℝ) (Ψ : ℂ → ℂ), Differentiable ℂ Ψ ∧
      ∀ s : ℂ, σ₀ < s.re →
        MellinConvergent (fun y : ℝ => f y) s ∧
          mellin (fun y : ℝ => f y) s = Complex.Gammaℂ (s + (c₀ - (P.centralExponent - 1) / 2)) * Ψ s) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_ArchDatumR_negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen.solution
