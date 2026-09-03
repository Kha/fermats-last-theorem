import Mathlib
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import P2M.Util
import P2M.Sol.S_ValuationSubring_valuation_completion_smul_sub_self_lt_one_of_mem_inertiaSubgroup

theorem ValuationSubring.valuation_completion_smul_sub_self_lt_one_of_mem_inertiaSubgroup
    {F K : Type*} [Field F] [Field K] [Algebra F K] (A : ValuationSubring K)
    [Fact (A.DecompositionIsometric F)]
    {σ : A.decompositionSubgroup F} (hσ : σ ∈ A.inertiaSubgroup F)
    (x : A.valuation.Completion) (hx : Valued.v x ≤ 1) :
    Valued.v (σ • x - x) < 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_valuation_completion_smul_sub_self_lt_one_of_mem_inertiaSubgroup.solution
