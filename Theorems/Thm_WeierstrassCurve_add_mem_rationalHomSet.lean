import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_add_mem_rationalHomSet

theorem WeierstrassCurve.add_mem_rationalHomSet {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] {α β : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hβ : β ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) : α + β ∈ WeierstrassCurve.rationalHomSet k W₁ W₂ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_add_mem_rationalHomSet.solution
