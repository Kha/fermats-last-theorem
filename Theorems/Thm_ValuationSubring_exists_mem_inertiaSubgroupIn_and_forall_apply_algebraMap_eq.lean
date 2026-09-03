import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mem_inertiaSubgroupIn_and_forall_apply_algebraMap_eq

set_option autoImplicit false

universe u

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_and_forall_apply_algebraMap_eq
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L]
    {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [Normal K Ω]
    (A₀ : ValuationSubring L) (τ : L ≃ₐ[K] L) (hτ : τ ∈ A₀.inertiaSubgroupIn K) :
    ∃ (A : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω),
      A.comap (algebraMap L Ω) = A₀ ∧ σ ∈ A.inertiaSubgroupIn K ∧
        ∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω (τ x) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_and_forall_apply_algebraMap_eq.solution
