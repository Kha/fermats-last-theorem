import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_uniform_pow_mul_mem_of_liesOverPrime

set_option autoImplicit false

theorem ValuationSubring.exists_uniform_pow_mul_mem_of_liesOverPrime {p : ℕ} (hp : p.Prime)
    {x : AlgebraicClosure ℚ} (hx : x ≠ 0) :
    ∃ B : ℕ, ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      (p : AlgebraicClosure ℚ) ^ B * x ∈ A ∧ (p : AlgebraicClosure ℚ) ^ B * x⁻¹ ∈ A := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_uniform_pow_mul_mem_of_liesOverPrime.solution
