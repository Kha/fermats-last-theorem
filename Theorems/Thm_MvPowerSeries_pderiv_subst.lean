import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_MvPowerSeries_pderiv_subst

set_option autoImplicit false

open FormalGroup

theorem MvPowerSeries.pderiv_subst
    {σ : Type*} {R : Type*} [CommRing R] (i : σ) (a : MvPowerSeries σ R)
    (ha : MvPowerSeries.constantCoeff a = 0) (h : PowerSeries R) :
    MvPowerSeries.pderivLin i (PowerSeries.subst a h) =
      PowerSeries.subst a (PowerSeries.derivative R h) * MvPowerSeries.pderivLin i a := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_pderiv_subst.solution
