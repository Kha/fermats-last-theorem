import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_whittaker_ode_splitTorus_of_casimir_of_archWeightChar_of_unipotent

set_option autoImplicit false

open scoped Real
open AutomorphicForm

theorem LanglandsTunnell.whittaker_ode_splitTorus_of_casimir_of_archWeightChar_of_unipotent
    (F : GL (Fin 2) ℝ → ℂ) (k₀ : ℤ) (ν : ℂ)
    (hF : ContDiffOn ℝ 2
      (fun e : Fin 2 → Fin 2 → ℝ =>
        F (if h : (Matrix.of e).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h
          else 1))
      {e | (Matrix.of e).det ≠ 0})
    (hψ : ∀ (x : ℝ) (m : GL (Fin 2) ℝ),
      F (unipotentGL2 x * m) = Complex.exp (2 * Real.pi * Complex.I * x) * F m)
    (hk : ∀ (k : rowIsometrySubgroup₀ ℝ) (m : GL (Fin 2) ℝ),
      F (m * k) = (archWeightCharℝ k₀ k : ℂ) * F m)
    (hΩ : ∀ m : GL (Fin 2) ℝ,
      -((1 / 4 : ℂ) * deriv (fun t : ℝ => deriv (fun s : ℝ =>
            F (m * archFlowMatrix ArchDir.H t * archFlowMatrix ArchDir.H s)) 0) 0
          - (1 / 2 : ℂ) * deriv (fun t : ℝ => F (m * archFlowMatrix ArchDir.H t)) 0
          + deriv (fun t : ℝ => deriv (fun s : ℝ =>
            F (m * archFlowMatrix ArchDir.E t * archFlowMatrix ArchDir.Fm s)) 0) 0)
        = (1 / 4 - ν ^ 2) * F m) :
    (DifferentiableOn ℝ (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2))) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2)))) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2)))) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((k₀ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * F (splitTorusGL2 (Real.log y / 2)) = 0) ∧
    (DifferentiableOn ℝ (fun y : ℝ => F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2))) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun y : ℝ => F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2))))
        (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)))) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (((-k₀ : ℤ) : ℝ) : ℂ) * (y : ℂ)
                - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) = 0) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_whittaker_ode_splitTorus_of_casimir_of_archWeightChar_of_unipotent.solution
