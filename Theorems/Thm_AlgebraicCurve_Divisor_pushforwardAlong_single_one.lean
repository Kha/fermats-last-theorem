import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_pushforwardAlong_single_one

set_option autoImplicit false

theorem AlgebraicCurve.Divisor.pushforwardAlong_single_one
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral) (W : AlgebraicCurve.Place K F')
    (hW : W.deg = 1) (hV : (W.restrictAlong ψ hψ).deg = 1) :
    AlgebraicCurve.Divisor.pushforwardAlong ψ hψ (Finsupp.single W 1) =
      Finsupp.single (W.restrictAlong ψ hψ) 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_single_one.solution
