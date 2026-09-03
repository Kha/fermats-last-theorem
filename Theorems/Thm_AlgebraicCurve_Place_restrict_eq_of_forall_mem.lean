import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_restrict_eq_of_forall_mem

theorem AlgebraicCurve.Place.restrict_eq_of_forall_mem {K F L : Type*} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L] [Algebra.IsIntegral F L]
    (w : AlgebraicCurve.Place K F) (Q : AlgebraicCurve.Place K L)
    (hQ : ∀ y ∈ w.toValuationSubring, algebraMap F L y ∈ Q.toValuationSubring) :
    Q.restrict F = w := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_restrict_eq_of_forall_mem.solution
