import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_laurentFrame_wUnitFactor

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.laurentFrame_wUnitFactor
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    (-(HahnSeries.single (-3 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor)) ^ 2 + HahnSeries.C W.a₁ * (HahnSeries.single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor) * (-(HahnSeries.single (-3 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor)) + HahnSeries.C W.a₃ * (-(HahnSeries.single (-3 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor))
        = (HahnSeries.single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor) ^ 3 + HahnSeries.C W.a₂ * (HahnSeries.single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor) ^ 2 + HahnSeries.C W.a₄ * (HahnSeries.single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor) + HahnSeries.C W.a₆ ∧
    (HahnSeries.single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor).coeff (-2) = 1 ∧ (∀ n < -2, (HahnSeries.single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor).coeff n = 0) ∧
    (-(HahnSeries.single (-3 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor)).coeff (-3) = -1 ∧ (∀ n < -3, (-(HahnSeries.single (-3 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor)).coeff n = 0) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_laurentFrame_wUnitFactor.solution
