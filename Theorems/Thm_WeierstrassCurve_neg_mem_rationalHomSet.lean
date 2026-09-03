import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_neg_mem_rationalHomSet

set_option autoImplicit false

theorem WeierstrassCurve.neg_mem_rationalHomSet
    {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [DecidableEq k]
    (W₁ W₂ : WeierstrassCurve F)
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) :
    -α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_neg_mem_rationalHomSet.solution
