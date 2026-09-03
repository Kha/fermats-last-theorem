import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_deg_cuspZeroBar

open ModularCurve AlgebraicCurve

theorem ModularCurve.deg_cuspZeroBar (N : ℕ) [NeZero N] : (cuspZeroBar N).deg = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_deg_cuspZeroBar.solution
