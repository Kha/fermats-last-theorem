import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_ArchDatumR_continuousOn_and_exists_ne_zero_W_diagOne_of_weightZero

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

open LanglandsTunnell.Converse.ArchR in

theorem LanglandsTunnell.Converse.ArchDatumR.continuousOn_and_exists_ne_zero_W_diagOne_of_weightZero
    {P : RealArchParam} (D : ArchDatumR P)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ 0 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0) :
    ContinuousOn (fun τ : ℝ => D.W (ArchR.diagOne τ)) {τ : ℝ | τ ≠ 0} ∧
      (∃ τ : ℝ, τ ≠ 0 ∧ D.W (ArchR.diagOne τ) ≠ 0) ∧
      0 < MeasureTheory.volume {τ : ℝ | D.W (ArchR.diagOne τ) ≠ 0} := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_ArchDatumR_continuousOn_and_exists_ne_zero_W_diagOne_of_weightZero.solution
