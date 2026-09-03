import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_mem_rationalEndSubring_iff_mem_rationalHomSet

set_option autoImplicit false

theorem WeierstrassCurve.mem_rationalEndSubring_iff_mem_rationalHomSet
    {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (α : AddMonoid.End (W.baseChange k).toAffine.Point) :
    α ∈ WeierstrassCurve.rationalEndSubring k W ↔
      (α : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) ∈
        WeierstrassCurve.rationalHomSet k W W := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_mem_rationalEndSubring_iff_mem_rationalHomSet.solution
