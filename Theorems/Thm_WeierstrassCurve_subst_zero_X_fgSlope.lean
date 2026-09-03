import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_subst_zero_X_fgSlope

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.subst_zero_X_fgSlope
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    MvPowerSeries.subst ![(0 : PowerSeries R), PowerSeries.X] W.fgSlope
      = PowerSeries.mk fun n => PowerSeries.coeff (n + 1) W.formalW := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_subst_zero_X_fgSlope.solution
