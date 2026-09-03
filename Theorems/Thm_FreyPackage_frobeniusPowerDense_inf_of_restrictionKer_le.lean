import Mathlib
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import P2M.Util
import P2M.Sol.S_FreyPackage_frobeniusPowerDense_inf_of_restrictionKer_le
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

theorem FreyPackage.frobeniusPowerDense_inf_of_restrictionKer_le (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    [Algebra F (AlgebraicClosure ℚ)] [IsScalarTower ℚ F (AlgebraicClosure ℚ)]
    {M : Type*} [MulOneClass M] (ρmat : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M)
    (H₂ : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hρ : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ ρmat.ker)
    (hH : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H₂) (Sρ : Finset ℕ) :
    FrobeniusPowerDense Sρ (ρmat.ker ⊓ H₂) := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_frobeniusPowerDense_inf_of_restrictionKer_le.solution
