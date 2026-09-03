import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_PeriodPair_Uniformization
import P2M.Util
import P2M.Sol.S_PeriodPair_exists_forall_apply_toPoint_eq_toPoint_mul_of_mem_rationalHomSet

theorem PeriodPair.exists_forall_apply_toPoint_eq_toPoint_mul_of_mem_rationalHomSet (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero) {α : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet ℂ L.weierstrassCurve L'.weierstrassCurve) : ∃ a : ℂ, ∀ z : ℂ, α (L.toPoint hL z) = L'.toPoint hL' (a * z) := by p2m_exact_reverting @_root_.P2MW.S_PeriodPair_exists_forall_apply_toPoint_eq_toPoint_mul_of_mem_rationalHomSet.solution
