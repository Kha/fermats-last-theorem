import Mathlib
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
set_option autoImplicit false

theorem FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker (F : Type) [Field F] [NumberField F]
    [IsGalois ℚ F] [Algebra F (AlgebraicClosure ℚ)]
    {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H)
    (S : Finset ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧ g * τ * g⁻¹ * σ⁻¹ ∈ H := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker.solution
