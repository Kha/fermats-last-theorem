import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_MapPoint
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_map_fullKernelQuotient_mapPoint

theorem WeierstrassCurve.map_fullKernelQuotient_mapPoint {F K : Type*} [Field F] [Field K]
    [DecidableEq F] [DecidableEq K] (W : WeierstrassCurve F) (f : F →+* K) (Q : W.toAffine.Point)
    (N : ℕ) :
    (W.map f).fullKernelQuotient (mapPoint f Q) N = (W.fullKernelQuotient Q N).map f := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_map_fullKernelQuotient_mapPoint.solution
