import Definitions.Def_AlgebraicCurve_Differentials
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_pullbackDiff_smul

open AlgebraicCurve
theorem AlgebraicCurve.pullbackDiff_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (g : F) (ω : Ω[F⁄K]) :
    pullbackDiff φ (g • ω) = φ g • pullbackDiff φ ω := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_pullbackDiff_smul.solution
