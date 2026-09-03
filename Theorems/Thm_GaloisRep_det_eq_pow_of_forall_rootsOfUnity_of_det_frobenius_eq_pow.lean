import Mathlib.Data.ZMod.Basic
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_GaloisRep_det_eq_pow_of_forall_rootsOfUnity_of_det_frobenius_eq_pow
attribute [-instance] AlgebraicClosure.Rat.isGalois FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

theorem GaloisRep.det_eq_pow_of_forall_rootsOfUnity_of_det_frobenius_eq_pow
    (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [CharP F p]
    (N : ℕ) [NeZero N] (S : Set ℕ) (hSfin : S.Finite) (m : ℕ)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (hdet : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          Matrix.det (ρ σ).val = (ℓ : F) ^ m)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
      (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) → Matrix.det (ρ σ).val = (a : F) ^ m := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_det_eq_pow_of_forall_rootsOfUnity_of_det_frobenius_eq_pow.solution
