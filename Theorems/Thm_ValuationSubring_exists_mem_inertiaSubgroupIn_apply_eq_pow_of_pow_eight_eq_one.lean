import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_eight_eq_one

set_option autoImplicit false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_eight_eq_one
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 2) (u : (ZMod 8)ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ 8 = 1 →
      σ μ = μ ^ ((u : ZMod 8)).val := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_eight_eq_one.solution
