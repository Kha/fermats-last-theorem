import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_U_powerSeries {W : Type*} [CommRing W] (π : W) : ∃ e : (UVCrossingModel W π ⧸ Ideal.span {U π}) ≃+* PowerSeries (W ⧸ Ideal.span {π}), e (Ideal.Quotient.mk _ (V π)) = PowerSeries.X ∧ e (Ideal.Quotient.mk _ (U π)) = 0 ∧ ∀ w : W, e (Ideal.Quotient.mk _ (const π w)) = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) w) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries.solution
