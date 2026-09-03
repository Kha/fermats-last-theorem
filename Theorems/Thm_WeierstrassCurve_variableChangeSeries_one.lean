import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_variableChangeSeries_one

set_option autoImplicit false

universe u

open FormalGroup IsLocalRing

theorem WeierstrassCurve.variableChangeSeries_one
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    W.variableChangeSeries 1 = PowerSeries.X := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_variableChangeSeries_one.solution
