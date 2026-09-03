import Definitions.Def_ModularCurve_UVCrossingChart
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_chartHom_X

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) :
    chartHom π PowerSeries.X = S π :=
  by
  rw [chartHom_apply, PowerSeries.subst_X (hasSubst_sAmbient W), sAmbient, map_add, S_def]
  rfl
