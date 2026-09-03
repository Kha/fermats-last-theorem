import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import Definitions.Def_AutomorphicForm_ArchWeightChar
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_PrincipalFamily_oddComb_archWeightChar
attribute [-simp] LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse AutomorphicForm

theorem LanglandsTunnell.Converse.PrincipalFamily.oddComb_archWeightChar (u₁ u₂ : ℂ) :
    ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      Wmem u₁ u₂ 1 0 ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) +
          Complex.I * (((SignType.sign ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det
            : ℝ) : ℂ) * Wmem u₁ u₂ 0 1 ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) =
        (archWeightCharℝ (1 : ℤ) r : ℂ) *
          (Wmem u₁ u₂ 1 0 (x : Matrix (Fin 2) (Fin 2) ℝ) +
            Complex.I * (((SignType.sign (x : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) *
              Wmem u₁ u₂ 0 1 (x : Matrix (Fin 2) (Fin 2) ℝ))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_PrincipalFamily_oddComb_archWeightChar.solution
