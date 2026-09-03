import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_ofPowerSeries_invDiff_mul_eq_derivative_laurentFrame

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.ofPowerSeries_invDiff_mul_eq_derivative_laurentFrame
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) (G : FormalGroup R)
    (hG : G.toPowerSeries = W.formalGroupLawFixed) :
    HahnSeries.ofPowerSeries ℤ R G.invDiff *
        (2 * (-(HahnSeries.single (-3 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor)) + HahnSeries.C W.a₁ * (HahnSeries.single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor) + HahnSeries.C W.a₃)
      = LaurentSeries.derivative R (HahnSeries.single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_ofPowerSeries_invDiff_mul_eq_derivative_laurentFrame.solution
