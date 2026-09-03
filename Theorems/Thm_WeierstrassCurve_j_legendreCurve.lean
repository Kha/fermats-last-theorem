import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_LegendreJ
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_j_legendreCurve

open WeierstrassCurve
theorem WeierstrassCurve.j_legendreCurve {K : Type*} [Field K] (t : K) [(legendreCurve t).IsElliptic] :
    (legendreCurve t).j = ModularCurve.legendreJ t := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_j_legendreCurve.solution
