import Mathlib
import Definitions.Def_ModularCurve_X1Diamond
import P2M.Util
import P2M.Sol.S_ModularCurve_diamondOneBar_comm

theorem ModularCurve.diamondOneBar_comm (M d e : ℕ) :
    ModularCurve.diamondOneBar M d * ModularCurve.diamondOneBar M e =
      ModularCurve.diamondOneBar M e * ModularCurve.diamondOneBar M d := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_diamondOneBar_comm.solution
