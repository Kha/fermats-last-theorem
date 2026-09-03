import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_variableChangeDenom_map_and_variableChangeSeries_map

set_option autoImplicit false

theorem WeierstrassCurve.variableChangeDenom_map_and_variableChangeSeries_map
    {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R)
    (f : R →+* S) :
    (W.map f).variableChangeDenom (C.map f) = PowerSeries.map f (W.variableChangeDenom C) ∧
      (W.map f).variableChangeSeries (C.map f) = PowerSeries.map f (W.variableChangeSeries C) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_variableChangeDenom_map_and_variableChangeSeries_map.solution
