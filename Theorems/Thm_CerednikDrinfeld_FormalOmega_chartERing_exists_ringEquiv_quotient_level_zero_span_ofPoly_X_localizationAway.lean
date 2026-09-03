import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_chartERing_exists_ringEquiv_quotient_level_zero_span_ofPoly_X_localizationAway

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.chartERing.exists_ringEquiv_quotient_level_zero_span_ofPoly_X_localizationAway
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ) (hπ : (Ideal.span ({π} : Set 𝒪)).IsMaximal) (hr : 1 < r) (i : Fin 2) :
    ∃ e : (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) ≃+*
        Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1),
      (∀ a : 𝒪, e (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a))) =
          algebraMap (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) _ (Ideal.Quotient.mk _ a)) ∧
      e (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i))))) =
          algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.X ()) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_exists_ringEquiv_quotient_level_zero_span_ofPoly_X_localizationAway.solution
