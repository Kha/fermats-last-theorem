import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_inertiaDegAlong_eq_one_of_isAlgClosed

set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.Place.inertiaDegAlong_eq_one_of_isAlgClosed
    {K F F' : Type*} [Field K] [IsAlgClosed K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [IsCurveOver K F] [Algebra.EssFiniteType K F] [IsCurveOver K F'] [Algebra.EssFiniteType K F']
    (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral) (W : Place K F') :
    W.inertiaDegAlong ψ hψ = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_inertiaDegAlong_eq_one_of_isAlgClosed.solution
