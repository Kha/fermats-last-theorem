import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_pushforwardAlong_single_one_of_isAlgClosed

set_option autoImplicit false

theorem AlgebraicCurve.Divisor.pushforwardAlong_single_one_of_isAlgClosed
    {K F F' : Type*} [Field K] [IsAlgClosed K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [AlgebraicCurve.IsCurveOver K F]
    (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong K ψ)
    (W : AlgebraicCurve.Place K F') :
    AlgebraicCurve.Divisor.pushforwardAlong ψ hψ (Finsupp.single W 1) =
      Finsupp.single (W.restrictAlong ψ hψ) 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_single_one_of_isAlgClosed.solution
