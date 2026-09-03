import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_mem_inertiaSubgroupIn_pointwise_smul_iff

open scoped Pointwise

theorem ValuationSubring.mem_inertiaSubgroupIn_pointwise_smul_iff
    {K L : Type} [Field K] [Field L] [Algebra K L]
    (g σ : L ≃ₐ[K] L) (A : ValuationSubring L) :
    σ ∈ (g • A).inertiaSubgroupIn K ↔ g⁻¹ * σ * g ∈ A.inertiaSubgroupIn K := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_mem_inertiaSubgroupIn_pointwise_smul_iff.solution
