import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_isDomain_quotient_span_V
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_isPrime_span_V

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) [IsDomain (W ⧸ Ideal.span {π})] :
    (Ideal.span {V π}).IsPrime :=
  by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact ModularCurve.UVCrossingModel.isDomain_quotient_span_V π
