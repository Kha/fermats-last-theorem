import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mem_inertiaSubgroupIn_restrictNormal_eq

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_restrictNormal_eq
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) [Normal K M]
    (A : ValuationSubring L) (τ : M ≃ₐ[K] M)
    (hτ : τ ∈ (A.comap (algebraMap M L)).inertiaSubgroupIn K) :
    ∃ σ : L ≃ₐ[K] L, σ ∈ A.inertiaSubgroupIn K ∧ σ.restrictNormal M = τ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_restrictNormal_eq.solution
