import Definitions.Def_ModularCurve_UVCrossingChart
import Theorems.Thm_ModularCurve_UVCrossingModel_crossingSwap_chartHom
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_range_chartHom_le_fixedSubring

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) :
    (chartHom π).range ≤ fixedSubring π :=
  by
  intro x hx
  obtain ⟨f, rfl⟩ := RingHom.mem_range.mp hx
  exact mem_fixedSubring_iff.mpr (ModularCurve.UVCrossingModel.crossingSwap_chartHom π f)
