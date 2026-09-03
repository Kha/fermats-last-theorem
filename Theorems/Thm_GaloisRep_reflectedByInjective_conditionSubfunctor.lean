import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ConjQuotSubfunctor
import P2M.Util
import P2M.Sol.S_GaloisRep_reflectedByInjective_conditionSubfunctor
attribute [-instance] Deformation.ProartinianCat.instFiniteResidueField Deformation.ProartinianCat.instCompactSpace

set_option autoImplicit false

open CategoryTheory IsLocalRing
theorem GaloisRep.reflectedByInjective_conditionSubfunctor
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (ρ₀ : (Deformation.repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj
      Deformation.ProartinianCat.residueField)
    [Finite (IsLocalRing.ResidueField 𝒪)]
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟) :
    Deformation.ReflectedByInjective (Fin 2) (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_reflectedByInjective_conditionSubfunctor.solution
