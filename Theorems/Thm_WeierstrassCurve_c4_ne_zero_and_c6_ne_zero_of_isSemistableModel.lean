import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_c4_ne_zero_and_c6_ne_zero_of_isSemistableModel

open WeierstrassCurve
theorem WeierstrassCurve.c4_ne_zero_and_c6_ne_zero_of_isSemistableModel (W : WeierstrassCurve ℤ) (hW : W.IsSemistableModel) : W.c₄ ≠ 0 ∧ W.c₆ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_c4_ne_zero_and_c6_ne_zero_of_isSemistableModel.solution
