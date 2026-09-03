import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mem_inertiaSubgroupIn_forall_apply_algebraMap_eq_of_isCyclotomicExtension

set_option autoImplicit false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_forall_apply_algebraMap_eq_of_isCyclotomicExtension
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    [Algebra L (AlgebraicClosure ℚ)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (s : L ≃ₐ[ℚ] L) :
    ∃ σ' ∈ Pl.inertiaSubgroupIn ℚ, ∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_forall_apply_algebraMap_eq_of_isCyclotomicExtension.solution
