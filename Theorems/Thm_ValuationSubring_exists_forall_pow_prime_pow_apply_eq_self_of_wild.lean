import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild

theorem ValuationSubring.exists_forall_pow_prime_pow_apply_eq_self_of_wild {q : ℕ} (hq : q.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F] :
    ∃ a : ℕ, ∀ x ∈ F, (σ ^ (q ^ a)) x = x := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild.solution
