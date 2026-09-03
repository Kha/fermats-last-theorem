import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ValuationSubring_apply_eq_self_of_pow_eq_prime_of_mem_inertiaSubgroupIn_of_cyc_eq_one

set_option autoImplicit false
theorem ValuationSubring.apply_eq_self_of_pow_eq_prime_of_mem_inertiaSubgroupIn_of_cyc_eq_one {q : ℕ} (hq : q.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ), μ ^ q = 1 →
      σ μ = μ ^ ((cyc σ : ZMod q).val))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hσc : cyc σ = 1)
    (α : AlgebraicClosure ℚ) (hα : α ^ (q - 1) = (q : AlgebraicClosure ℚ)) :
    σ α = α := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_apply_eq_self_of_pow_eq_prime_of_mem_inertiaSubgroupIn_of_cyc_eq_one.solution
