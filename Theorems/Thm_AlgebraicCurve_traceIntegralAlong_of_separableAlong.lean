import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_traceIntegralAlong_of_separableAlong

namespace AlgebraicCurve
theorem traceIntegralAlong_of_separableAlong {K : Type*} {F : Type*} {F' : Type*}
    [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ) :
    TraceIntegralAlong φ hφ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_traceIntegralAlong_of_separableAlong.solution
end AlgebraicCurve
