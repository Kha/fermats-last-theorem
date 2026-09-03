import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_subsingleton_of_forall_isPrincipal

open AlgebraicCurve
theorem AlgebraicCurve.Pic0.subsingleton_of_forall_isPrincipal (K F : Type*) [Field K] [Field F] [Algebra K F]
    (h : ∀ D : Divisor K F, Divisor.degree D = 0 → D.IsPrincipal) :
    Subsingleton (Pic0 K F) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_subsingleton_of_forall_isPrincipal.solution
