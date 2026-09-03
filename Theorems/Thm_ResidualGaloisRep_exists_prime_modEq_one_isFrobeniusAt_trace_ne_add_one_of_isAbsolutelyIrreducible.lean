import Mathlib
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_exists_prime_modEq_one_isFrobeniusAt_trace_ne_add_one_of_isAbsolutelyIrreducible
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

theorem ResidualGaloisRep.exists_prime_modEq_one_isFrobeniusAt_trace_ne_add_one_of_isAbsolutelyIrreducible
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (ρ : ResidualGaloisRep k) (hρ : ρ.IsAbsolutelyIrreducible)
    (N : ℕ) [NeZero N] (S : Finset ℕ) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ N ∧ ℓ ≡ 1 [MOD N] ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt σ ℓ ∧
        LinearMap.trace k ρ.V (ρ.ρ σ) ≠ (ℓ : k) + 1 := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_exists_prime_modEq_one_isFrobeniusAt_trace_ne_add_one_of_isAbsolutelyIrreducible.solution
