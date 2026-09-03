import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_PeriodPair_Uniformization
import P2M.Util
import P2M.Sol.S_PeriodPair_exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul

theorem PeriodPair.exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero) (a : ℂ) (ha : ∀ l ∈ L.lattice, a * l ∈ L'.lattice) : ∃ β ∈ WeierstrassCurve.rationalHomSet ℂ L.weierstrassCurve L'.weierstrassCurve, ∀ z : ℂ, β (L.toPoint hL z) = L'.toPoint hL' (a * z) := by p2m_exact_reverting @_root_.P2MW.S_PeriodPair_exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul.solution
