import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv

open AlgebraicCurve
theorem AlgebraicCurve.Pic0.forall_isPrincipal_of_ringEquiv {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
    (h : ∀ D : Divisor K F, Divisor.degree D = 0 → D.IsPrincipal)
    (D' : Divisor K F') (hD' : Divisor.degree D' = 0) :
    D'.IsPrincipal := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv.solution
