import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_ModPForms_ofPowerSeries_thetaPS_eq_thetaL_ofPowerSeries

set_option autoImplicit false

theorem ModPForms.ofPowerSeries_thetaPS_eq_thetaL_ofPowerSeries
    (K : Type) [Field K] (φ : PowerSeries K) :
    HahnSeries.ofPowerSeries ℤ K (ModPForms.thetaPS φ) =
      ModularCurve.thetaL K (HahnSeries.ofPowerSeries ℤ K φ) := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_ofPowerSeries_thetaPS_eq_thetaL_ofPowerSeries.solution
