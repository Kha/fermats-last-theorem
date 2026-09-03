import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_existsUnique_normalForm

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.existsUnique_normalForm
    {W : Type u} [CommRing W] (ϖ : W) [IsAdicComplete (Ideal.span {ϖ}) W] (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) :
    ∃! ab : PowerSeries W × PowerSeries W,
      PowerSeries.constantCoeff ab.2 = 0 ∧ mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_existsUnique_normalForm.solution
