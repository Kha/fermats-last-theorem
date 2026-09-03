import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpansionDiffAlong_D

theorem ModularCurve.qExpansionDiffAlong_D {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) (x : F) : qExpansionDiffAlong σ (KaehlerDifferential.D K F x) = thetaL L (σ x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpansionDiffAlong_D.solution
