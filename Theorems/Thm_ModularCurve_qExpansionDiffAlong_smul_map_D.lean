import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpansionDiffAlong_smul_map_D

theorem ModularCurve.qExpansionDiffAlong_smul_map_D {K F F' L : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Field L] [Algebra K L] (σ : F' →ₐ[K] LaurentSeries L) (h : F') (x : F) : qExpansionDiffAlong σ (h • KaehlerDifferential.map K K F F' (KaehlerDifferential.D K F x)) = σ h * thetaL L (σ (algebraMap F F' x)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpansionDiffAlong_smul_map_D.solution
