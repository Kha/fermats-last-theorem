import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_coeff_one_variableChangeSeries

set_option autoImplicit false

theorem WeierstrassCurve.coeff_one_variableChangeSeries
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) :
    PowerSeries.coeff 1 (W.variableChangeSeries C) = (C.u : R) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_coeff_one_variableChangeSeries.solution
