import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_polynomial_rep_of_injective_of_mem_rationalHomSet

theorem WeierstrassCurve.exists_polynomial_rep_of_injective_of_mem_rationalHomSet
    {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic]
    (u : (W.baseChange k).toAffine.Point →+ (W'.baseChange k).toAffine.Point)
    (hu : u ∈ WeierstrassCurve.rationalHomSet k W W') (hinj : Function.Injective u) :
    ∃ (pX qX pY qY : Polynomial k) (B : Set k), B.Finite ∧
      ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B →
        ∃ h', u (.some x y h) =
          .some (pX.eval x + qX.eval x * y) (pY.eval x + qY.eval x * y) h' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_polynomial_rep_of_injective_of_mem_rationalHomSet.solution
