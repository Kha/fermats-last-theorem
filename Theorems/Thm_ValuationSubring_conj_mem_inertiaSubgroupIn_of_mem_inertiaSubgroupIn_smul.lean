import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul

open scoped Pointwise
theorem ValuationSubring.conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (g : L ≃ₐ[K] L) {σ : L ≃ₐ[K] L} (hσ : σ ∈ (g • A).inertiaSubgroupIn K) :
    g⁻¹ * σ * g ∈ A.inertiaSubgroupIn K := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul.solution
