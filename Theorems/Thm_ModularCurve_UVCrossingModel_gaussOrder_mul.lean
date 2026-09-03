import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_gaussOrder_mul

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.gaussOrder_mul
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e t : ℕ) (he : 1 ≤ e) (ht : t ≤ e)
    (x y : UVCrossingModel W (ϖ ^ e)) :
    gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t (x * y) =
      gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t x +
        gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_gaussOrder_mul.solution
