import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ConjQuotSubfunctor
import P2M.Util
import P2M.Sol.S_GaloisRep_conditionSubfunctor_le_liftFunctor

set_option autoImplicit false

open CategoryTheory IsLocalRing
theorem GaloisRep.conditionSubfunctor_le_liftFunctor
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (ρ₀ : (Deformation.repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj
      Deformation.ProartinianCat.residueField) :
    GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀ ≤
      Deformation.liftFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪 ρ₀ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_conditionSubfunctor_le_liftFunctor.solution
