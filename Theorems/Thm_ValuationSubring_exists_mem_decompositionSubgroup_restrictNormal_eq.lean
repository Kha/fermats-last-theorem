import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mem_decompositionSubgroup_restrictNormal_eq

open scoped Pointwise

theorem ValuationSubring.exists_mem_decompositionSubgroup_restrictNormal_eq
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) [Normal K M]
    (A : ValuationSubring L) (τ : M ≃ₐ[K] M)
    (hτ : τ • (A.comap (algebraMap M L)) = A.comap (algebraMap M L)) :
    ∃ σ : L ≃ₐ[K] L, σ ∈ A.decompositionSubgroup K ∧ σ.restrictNormal M = τ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_decompositionSubgroup_restrictNormal_eq.solution
