import Definitions.Def_ModularCurve_MultCoveringCharts
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_jpF_eq_jqFun

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.jpF_eq_jqFun (p : ℕ) [Fact p.Prime] : jpF p = PlaceSpecialization.jqFun (q := p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_jpF_eq_jqFun.solution
