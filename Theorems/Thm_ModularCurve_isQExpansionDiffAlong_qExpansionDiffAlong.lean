import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_ModularCurve_isQExpansionDiffAlong_qExpansionDiffAlong

theorem ModularCurve.isQExpansionDiffAlong_qExpansionDiffAlong {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) : IsQExpansionDiffAlong σ (qExpansionDiffAlong σ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isQExpansionDiffAlong_qExpansionDiffAlong.solution
