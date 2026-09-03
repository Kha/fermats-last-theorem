import Mathlib
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

theorem ResidualGaloisRep.exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible
    {k : Type} [Field k] (ρ : ResidualGaloisRep k) (hρ : ρ.IsAbsolutelyIrreducible)
    (N : ℕ) [NeZero N] {M : ℕ} (hM : 0 < M) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ≡ 1 [MOD N] ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt σ ℓ ∧
        (LinearMap.charpoly (ρ.ρ σ)).eval 1 ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible.solution
