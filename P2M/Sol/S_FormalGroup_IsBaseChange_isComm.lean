import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
namespace P2MW.S_FormalGroup_IsBaseChange_isComm

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem solution
    {R S : Type*} [CommRing R] [CommRing S] (F : FormalGroup R) (f : R →+* S) (G : FormalGroup S)
    (h : F.IsBaseChange f G) [F.IsComm] : G.IsComm := by
  refine ⟨?_⟩
  unfold FormalGroup.IsBaseChange at h
  have hc : (F.toPowerSeries : MvPowerSeries (Fin 2) R) =
      (F.toPowerSeries).subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] := FormalGroup.IsComm.comm
  have hv : (fun i : Fin 2 => ((![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R) i).map f) =
      (![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) S) := by
    funext i; fin_cases i <;> simp [MvPowerSeries.map_X]
  show G.toPowerSeries = G.toPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0]
  rw [h]
  conv_lhs => rw [hc]
  rw [MvPowerSeries.map_subst MvPowerSeries.HasSubst.X_X, hv]
