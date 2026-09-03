import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_ArchDatumR_laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.ArchDatumR.laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen
    (P : RealArchParam) (D : ArchDatumR P) (k : ℤ) (ν : ℂ) (hν : ν ^ 2 = 1 / 4 - P.laplaceEigenvalue)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D) :
    let B : Matrix (Fin 2) (Fin 2) ℝ → ℂ := fun x => (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W x
    (∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 → B (ArchR.unip t * x) = ArchR.psi t * B x) ∧
    (∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → x.det ≠ 0 → B (t • x) = ((t : ℂ) ^ P.centralExponent) * B x) ∧
    (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      B ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * B (x : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      DifferentiableOn ℝ (fun y : ℝ => B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun y : ℝ => B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])) (Set.Ioi 0) ∧
      (∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])) y
            + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((ε * k : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] = 0) ∧
      ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]‖ ≤ C * y ^ N) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_ArchDatumR_laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen.solution
