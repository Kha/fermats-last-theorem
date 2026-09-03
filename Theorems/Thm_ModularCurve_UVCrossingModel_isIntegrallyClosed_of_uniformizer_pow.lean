import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
theorem ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) :
    IsDomain (UVCrossingModel W (ϖ ^ e)) ∧ IsLocalRing (UVCrossingModel W (ϖ ^ e)) ∧ IsIntegrallyClosed (UVCrossingModel W (ϖ ^ e)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow.solution
