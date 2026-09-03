import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
set_option autoImplicit false

open ModularCurve
theorem ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) :
    IsDomain (UVCrossingModel W (ϖ ^ e)) ∧ IsLocalRing (UVCrossingModel W (ϖ ^ e)) ∧
      IsIntegrallyClosed (UVCrossingModel W (ϖ ^ e)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete.solution
