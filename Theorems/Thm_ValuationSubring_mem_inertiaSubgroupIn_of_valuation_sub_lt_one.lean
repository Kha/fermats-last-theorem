import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_mem_inertiaSubgroupIn_of_valuation_sub_lt_one

open scoped Pointwise
theorem ValuationSubring.mem_inertiaSubgroupIn_of_valuation_sub_lt_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) {σ : L ≃ₐ[K] L} (hσA : σ • A = A)
    (h : ∀ a ∈ A, A.valuation (σ a - a) < 1) :
    σ ∈ A.inertiaSubgroupIn K := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_mem_inertiaSubgroupIn_of_valuation_sub_lt_one.solution
