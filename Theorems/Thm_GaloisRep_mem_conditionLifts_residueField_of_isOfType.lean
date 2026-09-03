import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ProartinianCompact
import P2M.Util
import P2M.Sol.S_GaloisRep_mem_conditionLifts_residueField_of_isOfType

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits IsLocalRing Deformation Deformation.ProartinianCat
theorem GaloisRep.mem_conditionLifts_residueField_of_isOfType
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    (ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) (Deformation.ProartinianCat.residueField (𝓞 := 𝒪)))
    (b : Module.Basis (Fin 2) (IsLocalRing.ResidueField 𝒪) ρbar.V)
    (hρ₀ : ∀ σ, (ρ₀ σ).val = LinearMap.toMatrix b b (ρbar.ρ σ))
    (hbar : 𝒟 (GaloisRepAdic.ofResidualGaloisRep ρbar)) :
    ρ₀ ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ Deformation.ProartinianCat.residueField := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_mem_conditionLifts_residueField_of_isOfType.solution
