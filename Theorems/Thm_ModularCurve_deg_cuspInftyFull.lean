import Definitions.Def_ModularCurve_QAdicPlace
import P2M.Util
import P2M.Sol.S_ModularCurve_deg_cuspInftyFull

open ModularCurve AlgebraicCurve

theorem ModularCurve.deg_cuspInftyFull (N : ℕ) [NeZero N] : (cuspInftyFull N).deg = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_deg_cuspInftyFull.solution
