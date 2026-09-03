import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_exists_archDatumR_oddArtin_archWeightChar_one_mdifferentiable_W_ne_zero

set_option autoImplicit false

open AutomorphicForm

theorem LanglandsTunnell.Converse.exists_archDatumR_oddArtin_archWeightChar_one_mdifferentiable_W_ne_zero :
    ∃ d : ArchDatumR RealArchParam.oddArtin,
      (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        d.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ 1 r : ℂ) * d.W (x : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      (∀ (x : GL (Fin 2) ℝ),
        MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) fun z : UpperHalfPlane =>
          ((z.im : ℝ) : ℂ)⁻¹ *
            d.W ((x * iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      ∃ g : GL (Fin 2) ℝ, d.W g ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_exists_archDatumR_oddArtin_archWeightChar_one_mdifferentiable_W_ne_zero.solution
