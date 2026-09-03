import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_raising_lowering_splitTorus_of_archWeightChar_of_unipotent

set_option autoImplicit false

open scoped Real
open AutomorphicForm

theorem LanglandsTunnell.raising_lowering_splitTorus_of_archWeightChar_of_unipotent (F : GL (Fin 2) ℝ → ℂ) (k₀ : ℤ)
    (hF : ContDiffOn ℝ 1
      (fun e : Fin 2 → Fin 2 → ℝ =>
        F (if h : (Matrix.of e).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h
          else 1))
      {e | (Matrix.of e).det ≠ 0})
    (hψ : ∀ (x : ℝ) (m : GL (Fin 2) ℝ),
      F (unipotentGL2 x * m) = Complex.exp (2 * Real.pi * Complex.I * x) * F m)
    (hk : ∀ (k : rowIsometrySubgroup₀ ℝ) (m : GL (Fin 2) ℝ),
      F (m * k) = (archWeightCharℝ k₀ k : ℂ) * F m) :
    DifferentiableOn ℝ (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2))) (Set.Ioi 0) ∧
    DifferentiableOn ℝ (fun y : ℝ => F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2))) (Set.Ioi 0) ∧
    ∀ y : ℝ, 0 < y →
      (deriv (fun t : ℝ => F (splitTorusGL2 (Real.log y / 2) * archFlowMatrix ArchDir.H t)) 0
          + Complex.I * (deriv (fun t : ℝ => F (splitTorusGL2 (Real.log y / 2) * archFlowMatrix ArchDir.E t)) 0
            + deriv (fun t : ℝ => F (splitTorusGL2 (Real.log y / 2) * archFlowMatrix ArchDir.Fm t)) 0)
        = 2 * (y : ℂ) * deriv (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2))) y
          - (4 * (π : ℂ) * (y : ℂ) - (k₀ : ℂ)) * F (splitTorusGL2 (Real.log y / 2))) ∧
      (deriv (fun t : ℝ => F (splitTorusGL2 (Real.log y / 2) * archFlowMatrix ArchDir.H t)) 0
          - Complex.I * (deriv (fun t : ℝ => F (splitTorusGL2 (Real.log y / 2) * archFlowMatrix ArchDir.E t)) 0
            + deriv (fun t : ℝ => F (splitTorusGL2 (Real.log y / 2) * archFlowMatrix ArchDir.Fm t)) 0)
        = 2 * (y : ℂ) * deriv (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2))) y
          + (4 * (π : ℂ) * (y : ℂ) - (k₀ : ℂ)) * F (splitTorusGL2 (Real.log y / 2))) ∧
      (deriv (fun t : ℝ => F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2) * archFlowMatrix ArchDir.H t)) 0
          + Complex.I * (deriv (fun t : ℝ =>
              F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2) * archFlowMatrix ArchDir.E t)) 0
            + deriv (fun t : ℝ =>
              F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2) * archFlowMatrix ArchDir.Fm t)) 0)
        = 2 * (y : ℂ) * deriv (fun y : ℝ => F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2))) y
          + (4 * (π : ℂ) * (y : ℂ) + (k₀ : ℂ)) * F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2))) ∧
      (deriv (fun t : ℝ => F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2) * archFlowMatrix ArchDir.H t)) 0
          - Complex.I * (deriv (fun t : ℝ =>
              F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2) * archFlowMatrix ArchDir.E t)) 0
            + deriv (fun t : ℝ =>
              F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2) * archFlowMatrix ArchDir.Fm t)) 0)
        = 2 * (y : ℂ) * deriv (fun y : ℝ => F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2))) y
          - (4 * (π : ℂ) * (y : ℂ) + (k₀ : ℂ)) * F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_raising_lowering_splitTorus_of_archWeightChar_of_unipotent.solution
