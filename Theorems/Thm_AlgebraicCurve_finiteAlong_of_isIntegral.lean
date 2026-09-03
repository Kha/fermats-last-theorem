import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_finiteAlong_of_isIntegral

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.finiteAlong_of_isIntegral
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra.EssFiniteType K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) :
    FiniteAlong K φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_finiteAlong_of_isIntegral.solution
