import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_V_notMem_span_U

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) [Nontrivial (W ⧸ Ideal.span {π})] :
    V π ∉ Ideal.span {U π} :=
  by
  obtain ⟨e, heV, -, -⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_U_powerSeries π
  intro hmem
  apply PowerSeries.X_ne_zero (R := W ⧸ Ideal.span {π})
  rw [← heV, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
