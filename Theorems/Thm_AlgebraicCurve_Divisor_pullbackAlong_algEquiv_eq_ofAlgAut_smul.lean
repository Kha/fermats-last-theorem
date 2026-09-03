import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul

theorem AlgebraicCurve.Divisor.pullbackAlong_algEquiv_eq_ofAlgAut_smul
    {K F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.HasPrincipalDivisors K F]
    (σ : F ≃ₐ[K] F) (hσ : (σ : F →ₐ[K] F).toRingHom.IsIntegral) (D : AlgebraicCurve.Divisor K F) :
    AlgebraicCurve.Divisor.pullbackAlong (σ : F →ₐ[K] F) hσ D = AlgebraicCurve.SemilinearAut.ofAlgAut σ • D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul.solution
