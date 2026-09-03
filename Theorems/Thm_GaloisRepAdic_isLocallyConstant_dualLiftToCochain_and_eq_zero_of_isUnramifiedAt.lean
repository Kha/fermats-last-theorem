import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GroupCohomology_TangentSpace
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isLocallyConstant_dualLiftToCochain_and_eq_zero_of_isUnramifiedAt

set_option autoImplicit false

open groupCohomology TrivSqZeroExt

theorem GaloisRepAdic.isLocallyConstant_dualLiftToCochain_and_eq_zero_of_isUnramifiedAt
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k) (ρA : GaloisRepAdic (DualNumber k))
    (ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (DualNumber (Module.End k ρbar.V))ˣ)
    (hd : IsDualLift ρbar.ρ.toHomUnits ρd)
    (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V)
    (hfr : ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
      Matrix.dualNumberEquiv.symm
        ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
          LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩) :
    IsLocallyConstant (dualLiftToCochain ρbar.ρ.toHomUnits ρd) ∧
    (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, σ x = x) →
        dualLiftToCochain ρbar.ρ.toHomUnits ρd σ = 0) ∧
      (∀ g s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, s x = x) →
        dualLiftToCochain ρbar.ρ.toHomUnits ρd (g * s) =
          dualLiftToCochain ρbar.ρ.toHomUnits ρd g)) ∧
    ∀ q : ℕ, ρA.IsUnramifiedAt q →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, dualLiftToCochain ρbar.ρ.toHomUnits ρd σ = 0 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isLocallyConstant_dualLiftToCochain_and_eq_zero_of_isUnramifiedAt.solution
