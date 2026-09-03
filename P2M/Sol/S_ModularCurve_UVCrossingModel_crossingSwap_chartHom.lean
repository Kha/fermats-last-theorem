import Definitions.Def_ModularCurve_UVCrossingChart
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_crossingSwap_chartHom

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) (f : PowerSeries W) :
    crossingSwap π (chartHom π f) = chartHom π f :=
  by
  have hsw : ∀ f : PowerSeries W, uvSwapEquiv (PowerSeries.subst (sAmbient W) f) = PowerSeries.subst (sAmbient W) f := by
    intro f
    rw [uvSwapEquiv_apply, MvPowerSeries.rename_eq_subst, PowerSeries.subst_def,
      MvPowerSeries.subst_comp_subst_apply
        (PowerSeries.HasSubst.const (hasSubst_sAmbient W))
        (MvPowerSeries.HasSubst.X_comp _)]
    have h : (fun _ : Unit ↦ MvPowerSeries.subst
        (MvPowerSeries.X ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) (sAmbient W)) =
        (fun _ : Unit ↦ sAmbient W) := by
      funext _
      rw [← MvPowerSeries.rename_eq_subst, ← uvSwapEquiv_apply]
      rw [sAmbient, map_add, uvSwapEquiv_X_zero, uvSwapEquiv_X_one, add_comm]
    rw [h, ← PowerSeries.subst_def]
  rw [chartHom_apply, crossingSwap_mk, hsw]
