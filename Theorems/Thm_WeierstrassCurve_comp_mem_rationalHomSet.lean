import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_comp_mem_rationalHomSet

theorem WeierstrassCurve.comp_mem_rationalHomSet {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [DecidableEq k] (W₁ W₂ W₃ : WeierstrassCurve F) {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point} {β : (W₂.baseChange k).toAffine.Point →+ (W₃.baseChange k).toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hβ : β ∈ WeierstrassCurve.rationalHomSet k W₂ W₃) : β.comp α ∈ WeierstrassCurve.rationalHomSet k W₁ W₃ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_comp_mem_rationalHomSet.solution
