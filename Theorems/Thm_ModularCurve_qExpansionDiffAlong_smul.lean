import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpansionDiffAlong_smul

theorem ModularCurve.qExpansionDiffAlong_smul {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) (f : F) (ω : Ω[F⁄K]) : qExpansionDiffAlong σ (f • ω) = σ f * qExpansionDiffAlong σ ω := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpansionDiffAlong_smul.solution
