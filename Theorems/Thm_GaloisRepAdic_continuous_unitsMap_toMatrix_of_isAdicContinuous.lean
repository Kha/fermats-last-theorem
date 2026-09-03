import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_Deformations_ProartinianCat
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_continuous_unitsMap_toMatrix_of_isAdicContinuous

set_option autoImplicit false

open IsLocalRing
theorem GaloisRepAdic.continuous_unitsMap_toMatrix_of_isAdicContinuous
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    (A : Deformation.ProartinianCat 𝒪) [IsLocalRing.IsAdicTopology A]
    (ρ : GaloisRepAdic A) (b : Module.Basis (Fin 2) A ρ.V) :
    Continuous (fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ =>
      (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom (ρ.ρ.toHomUnits σ) :
        GL (Fin 2) A)) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_continuous_unitsMap_toMatrix_of_isAdicContinuous.solution
