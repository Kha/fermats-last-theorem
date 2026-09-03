import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_MvPowerSeries_pderiv_mul

set_option autoImplicit false

open FormalGroup

theorem MvPowerSeries.pderiv_mul
    {σ : Type*} {R : Type*} [CommRing R] (i : σ) (f g : MvPowerSeries σ R) :
    MvPowerSeries.pderivLin i (f * g) = MvPowerSeries.pderivLin i f * g + f * MvPowerSeries.pderivLin i g := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_pderiv_mul.solution
