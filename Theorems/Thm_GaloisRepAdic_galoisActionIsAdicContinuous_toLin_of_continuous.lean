import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_Deformations_LiftFunctor
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_galoisActionIsAdicContinuous_toLin_of_continuous

set_option autoImplicit false

open IsLocalRing
theorem GaloisRepAdic.galoisActionIsAdicContinuous_toLin_of_continuous
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    (A : Deformation.ProartinianCat 𝒪) [IsLocalRing.IsAdicTopology A]
    (ρ' : (Deformation.repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj A) :
    GaloisActionIsAdicContinuous A
      ((Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ'.toMonoidHom)) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_galoisActionIsAdicContinuous_toLin_of_continuous.solution
