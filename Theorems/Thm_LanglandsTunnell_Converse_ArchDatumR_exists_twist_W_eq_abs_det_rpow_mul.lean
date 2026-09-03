import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_ArchDatumR_exists_twist_W_eq_abs_det_rpow_mul

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse AutomorphicForm
theorem LanglandsTunnell.Converse.ArchDatumR.exists_twist_W_eq_abs_det_rpow_mul
    (P : RealArchParam) (D : ArchDatumR P) (t : ℝ) :
    ∃ D' : ArchDatumR (P.twist (t : ℂ) 0),
      (∀ g : Matrix (Fin 2) (Fin 2) ℝ, D'.W g = (((|g.det| ^ t : ℝ)) : ℂ) * D.W g) ∧
      (ArchCasimir.IsCasimirEigen D → ArchCasimir.IsCasimirEigen D') ∧
      (∀ k : ℤ, (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
          D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
            (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ)) →
        (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
          D'.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
            (archWeightCharℝ k r : ℂ) * D'.W (x : Matrix (Fin 2) (Fin 2) ℝ))) ∧
      ((∃ g : GL (Fin 2) ℝ, D.W g ≠ 0) → ∃ g : GL (Fin 2) ℝ, D'.W g ≠ 0) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_twist_W_eq_abs_det_rpow_mul.solution
