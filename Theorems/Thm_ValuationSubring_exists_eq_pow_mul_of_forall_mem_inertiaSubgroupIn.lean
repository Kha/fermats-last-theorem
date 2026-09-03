import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn

open scoped Pointwise

theorem ValuationSubring.exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn
    (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ((ℓ : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (c : AlgebraicClosure ℚ) (hcA : c ∈ A) (hc0 : c ≠ 0)
    (hc : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ → σ c = c) :
    ∃ (s : ℕ) (u : AlgebraicClosure ℚ), u ∈ A ∧ u⁻¹ ∈ A ∧ c = ((ℓ : ℕ) : AlgebraicClosure ℚ) ^ s * u := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn.solution
