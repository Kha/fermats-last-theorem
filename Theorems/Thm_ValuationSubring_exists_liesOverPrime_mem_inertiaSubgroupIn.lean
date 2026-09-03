import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_liesOverPrime_mem_inertiaSubgroupIn

theorem ValuationSubring.exists_liesOverPrime_mem_inertiaSubgroupIn (𝔔 : Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) [𝔔.IsMaximal] {q : ℕ} (hq : q.Prime) (hq𝔔 : (q : integralClosure ℤ (AlgebraicClosure ℚ)) ∈ 𝔔) (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : ∀ b : integralClosure ℤ (AlgebraicClosure ℚ), ∃ c ∈ 𝔔, (c : AlgebraicClosure ℚ) = σ b - b) : ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q ∧ σ ∈ A.inertiaSubgroupIn ℚ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_liesOverPrime_mem_inertiaSubgroupIn.solution
