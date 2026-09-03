import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Theorems.Thm_ModularCurve_UVCrossingModel_maximalIdeal_eq_span_pair
import Theorems.Thm_ModularCurve_UVCrossingModel_ringKrullDim_eq_two
import Theorems.Thm_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_isRegularLocalRing

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] [IsNoetherianRing W] [IsLocalRing W] [IsDomain W] {π : W} (hW : IsLocalRing.maximalIdeal W = Ideal.span {π}) (hπ0 : π ≠ 0) :
    IsRegularLocalRing (UVCrossingModel W π) :=
  by
  have hπu : ¬IsUnit π := by
    have : π ∈ IsLocalRing.maximalIdeal W := hW ▸ Ideal.mem_span_singleton_self π
    exact (IsLocalRing.mem_maximalIdeal _).mp this
  haveI : IsLocalRing (UVCrossingModel W π) := ModularCurve.UVCrossingModel.isLocalRing_of_not_isUnit hπu
  haveI : IsNoetherianRing (UVCrossingModel W π) := ModularCurve.UVCrossingModel.isNoetherianRing π
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [ModularCurve.UVCrossingModel.ringKrullDim_eq_two hW hπ0]

  have h2 : (IsLocalRing.maximalIdeal (UVCrossingModel W π)).spanFinrank ≤ 2 := by
    rw [ModularCurve.UVCrossingModel.maximalIdeal_eq_span_pair hW, ← Ideal.submodule_span_eq]
    refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)) ?_
    refine le_trans (Set.ncard_insert_le _ _) ?_
    simp [Set.ncard_singleton]
  exact_mod_cast h2
