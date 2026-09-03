import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_quotient_span_V

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_U_quotient_span_V {W : Type*} [CommRing W] (π : W) : ∃ e : (UVCrossingModel W π ⧸ Ideal.span {U π}) ≃+* (UVCrossingModel W π ⧸ Ideal.span {V π}), ∀ x : UVCrossingModel W π, e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (crossingSwap π x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_quotient_span_V.solution
