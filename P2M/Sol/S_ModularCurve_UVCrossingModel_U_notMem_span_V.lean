import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_V_powerSeries
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_U_notMem_span_V

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) [Nontrivial (W ⧸ Ideal.span {π})] :
    U π ∉ Ideal.span {V π} :=
  by
  obtain ⟨e, heU, -, -⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_V_powerSeries π
  intro hmem
  apply PowerSeries.X_ne_zero (R := W ⧸ Ideal.span {π})
  rw [← heU, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
