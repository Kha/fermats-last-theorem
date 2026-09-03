import Mathlib.RingTheory.Localization.FractionRing
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isUnipotentOnInertiaAt_of_tateModule_quotient

set_option autoImplicit false

open scoped TensorProduct

theorem GaloisRepAdic.isUnipotentOnInertiaAt_of_tateModule_quotient
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [IsLocalRing O] (ρ : GaloisRepAdic O)
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] [Algebra ℤ_[p] K]
    (π : K ⊗[ℤ_[p]] TateModule p M →ₗ[K] K ⊗[O] ρ.V) (hπ : Function.Surjective π)
    (hπρ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : K ⊗[ℤ_[p]] TateModule p M),
      π ((TateModule.rep p M (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange K x) =
        (ρ.ρ σ).baseChange K (π x))
    (q : ℕ)
    (hT : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ x : TateModule p M,
        TateModule.rep p M (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
            (TateModule.rep p M (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x - x) =
          TateModule.rep p M (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x - x) :
    ρ.IsUnipotentOnInertiaAt q := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isUnipotentOnInertiaAt_of_tateModule_quotient.solution
