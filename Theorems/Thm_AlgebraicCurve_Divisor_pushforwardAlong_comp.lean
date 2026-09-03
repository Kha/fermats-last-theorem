import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_pushforwardAlong_comp

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.pushforwardAlong_comp
    {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
    [Algebra K F] [Algebra K F'] [Algebra K F'']
    (φ : F →ₐ[K] F') (ψ : F' →ₐ[K] F'')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hψφ : (ψ.comp φ).toRingHom.IsIntegral)
    (D : Divisor K F'') :
    Divisor.pushforwardAlong (ψ.comp φ) hψφ D =
      Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong ψ hψ D) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_comp.solution
