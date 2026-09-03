import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_ringEquiv_apply_mk_X_mem_span_of_comp_eq_of_isUnit_det_one_sub

set_option autoImplicit false

theorem DrinfeldCurve.LocalChart.ringEquiv_apply_mk_X_mem_span_of_comp_eq_of_isUnit_det_one_sub
    (q : ℕ) [Fact q.Prime]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀]
    (t₀ : W₀) (f₀ u₀ v₀ : MvPowerSeries (Fin 2) W₀)
    (hf₀ : f₀ - DrinfeldCurve.LocalChart.drinfeldForm q W₀ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ (q + 2))
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (t : W) (ht : t ∈ IsLocalRing.maximalIdeal W) (f u v : MvPowerSeries (Fin 2) W)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (β : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}) ≃+*
      (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C t * v - f * u}))
    (βW : W₀ ≃+* W)
    (hβ : ∀ w : W₀, β (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = Ideal.Quotient.mk _ (MvPowerSeries.C (βW w)))

    (θ₀ : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}) ≃+*
      (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}))
    (θ : (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C t * v - f * u}) ≃+*
      (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C t * v - f * u}))
    (hint : ∀ s, β (θ₀ s) = θ (β s))
    (hθW : ∀ w : W, θ (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = Ideal.Quotient.mk _ (MvPowerSeries.C w))
    (hθJ : ∀ jj : Fin 2, θ (Ideal.Quotient.mk _ (MvPowerSeries.X jj)) ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 0),
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 1)})
    (M₀ : Matrix (Fin 2) (Fin 2) W₀)
    (hlin₀ : ∀ jj : Fin 2, θ₀ (Ideal.Quotient.mk _ (MvPowerSeries.X jj)) -
        Ideal.Quotient.mk _ (∑ ii : Fin 2, MvPowerSeries.C (M₀ ii jj) * MvPowerSeries.X ii) ∈
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}) (MvPowerSeries.X 0),
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}) (MvPowerSeries.X 1)}) ^ 2)
    (hdet : IsUnit (1 - M₀).det) :
    ∀ jj : Fin 2, β (Ideal.Quotient.mk _ (MvPowerSeries.X jj)) ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 0),
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 1)} := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_ringEquiv_apply_mk_X_mem_span_of_comp_eq_of_isUnit_det_one_sub.solution
