import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Util
import P2M.Sol.S_ModularCurve_deg_cuspInftyBar

open ModularCurve AlgebraicCurve

theorem ModularCurve.deg_cuspInftyBar (N : ℕ) [NeZero N] : (cuspInftyBar N).deg = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_deg_cuspInftyBar.solution
