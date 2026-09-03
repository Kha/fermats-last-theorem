import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn

theorem ValuationSubring.valuation_sub_lt_one_of_mem_inertiaSubgroupIn {K L : Type*} [Field K]
    [Field L] [Algebra K L] (A : ValuationSubring L) {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.inertiaSubgroupIn K) {a : L} (ha : a ∈ A) :
    σ a ∈ A ∧ A.valuation (σ a - a) < 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn.solution
