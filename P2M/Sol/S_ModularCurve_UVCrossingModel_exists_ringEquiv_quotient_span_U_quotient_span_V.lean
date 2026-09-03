import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_map_crossingSwap_span_U
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_quotient_span_V

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) :
    ∃ e : (UVCrossingModel W π ⧸ Ideal.span {U π}) ≃+* (UVCrossingModel W π ⧸ Ideal.span {V π}), ∀ x : UVCrossingModel W π, e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (crossingSwap π x) :=
  ⟨Ideal.quotientEquiv (Ideal.span {U π}) (Ideal.span {V π}) (crossingSwap π)
    (ModularCurve.UVCrossingModel.map_crossingSwap_span_U π).symm, fun _ => rfl⟩
