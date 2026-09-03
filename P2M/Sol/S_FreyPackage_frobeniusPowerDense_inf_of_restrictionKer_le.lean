import Mathlib
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import Theorems.Thm_FrobeniusDensity_frobeniusPowerDense_of_le_ker
import P2M.Util
namespace P2MW.S_FreyPackage_frobeniusPowerDense_inf_of_restrictionKer_le
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

theorem solution (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    [Algebra F (AlgebraicClosure ℚ)] [IsScalarTower ℚ F (AlgebraicClosure ℚ)]
    {M : Type*} [MulOneClass M] (ρmat : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M)
    (H₂ : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hρ : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ ρmat.ker)
    (hH : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H₂) (Sρ : Finset ℕ) :
    FrobeniusPowerDense Sρ (ρmat.ker ⊓ H₂) :=
  FrobeniusDensity.frobeniusPowerDense_of_le_ker F (le_inf hρ hH) Sρ
