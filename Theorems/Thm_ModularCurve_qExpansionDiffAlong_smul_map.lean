import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpansionDiffAlong_smul_map

theorem ModularCurve.qExpansionDiffAlong_smul_map {K F F' L : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Field L] [Algebra K L] (σ : F' →ₐ[K] LaurentSeries L) (h : F') (ω : Ω[F⁄K]) : qExpansionDiffAlong σ (h • KaehlerDifferential.map K K F F' ω) = σ h * qExpansionDiffAlong (σ.comp (IsScalarTower.toAlgHom K F F')) ω := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpansionDiffAlong_smul_map.solution
