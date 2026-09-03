import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import P2M.Util
namespace P2MW.S_WeierstrassCurve_variableChangeSeries_one

set_option autoImplicit false

universe u

open FormalGroup IsLocalRing

theorem solution
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    W.variableChangeSeries 1 = PowerSeries.X := by
  have hden : W.variableChangeDenom 1 = 1 := by
    simp [WeierstrassCurve.variableChangeDenom, WeierstrassCurve.VariableChange.one_def]
  rw [WeierstrassCurve.variableChangeSeries, hden]
  have hinv : PowerSeries.invOfUnit (1 : PowerSeries R) 1 = 1 := by
    have h := PowerSeries.mul_invOfUnit (1 : PowerSeries R) 1 (by simp)
    rwa [one_mul] at h
  rw [hinv]
  simp [WeierstrassCurve.VariableChange.one_def]
