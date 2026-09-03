import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_chartERing_eq_span_xi_or_eq_span_eta_of_mem_minimalPrimes_level_zero

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.chartERing.eq_span_xi_or_eq_span_eta_of_mem_minimalPrimes_level_zero
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ) (hπ : (Ideal.span ({π} : Set 𝒪)).IsMaximal)
    (P : Ideal ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})))
    (hP : P ∈ minimalPrimes ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}))) :
    P = Ideal.span {Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)} ∨ P = Ideal.span {Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)} := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_eq_span_xi_or_eq_span_eta_of_mem_minimalPrimes_level_zero.solution
