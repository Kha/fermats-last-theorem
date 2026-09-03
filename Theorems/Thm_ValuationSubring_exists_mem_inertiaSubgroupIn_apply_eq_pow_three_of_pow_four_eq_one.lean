import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_three_of_pow_four_eq_one

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_three_of_pow_four_eq_one
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 2) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ 4 = 1 → σ ζ = ζ ^ 3 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_three_of_pow_four_eq_one.solution
