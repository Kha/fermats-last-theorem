import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_isDiscreteValuationRing_quotient_branchPrime_of_sub_drinfeldForm_mem_pow

set_option autoImplicit false

theorem DrinfeldCurve.LocalChart.isDiscreteValuationRing_quotient_branchPrime_of_sub_drinfeldForm_mem_pow
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : IsLocalRing.maximalIdeal W = Ideal.span {π})
    (hqW : (q : W) ∈ IsLocalRing.maximalIdeal W)
    (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) (hc0 : c ≠ 0)
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (P : Ideal (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u})) [P.IsPrime]
    (hPX : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 0) ∉ P ∨
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 1) ∉ P)
    (hPπ : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.C π) ∈ P) :
    IsDiscreteValuationRing ((MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u}) ⧸ P) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_isDiscreteValuationRing_quotient_branchPrime_of_sub_drinfeldForm_mem_pow.solution
