import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Differential_pullbackAlong_comp

theorem AlgebraicCurve.Differential.pullbackAlong_comp
    {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F'']
    (φ : F →ₐ[K] F') (ψ : F' →ₐ[K] F'') (ω : Ω[F⁄K]) :
    AlgebraicCurve.Differential.pullbackAlong (ψ.comp φ) ω =
      AlgebraicCurve.Differential.pullbackAlong ψ (AlgebraicCurve.Differential.pullbackAlong φ ω) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Differential_pullbackAlong_comp.solution
