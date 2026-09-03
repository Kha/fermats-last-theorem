import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn

theorem ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn {q : ℕ} (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {n : ℕ} (hn : ¬ q ∣ n) {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ n = 1) : σ ζ = ζ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn.solution
