import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    (W.formalW * (PowerSeries.C W.a₃ * W.formalW + PowerSeries.C W.a₁ * PowerSeries.X - 2)) = (W.formalW - PowerSeries.X * PowerSeries.derivative R W.formalW) * MvPowerSeries.subst ![(0 : PowerSeries R), PowerSeries.X]
        (MvPowerSeries.pderivLin 0 W.formalGroupLawFixed) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed.solution
