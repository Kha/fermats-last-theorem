import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_eq_mul
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open IsLocalRing FormalGroup

theorem IsRegularLocalRing.exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_eq_mul
    (q : ℕ) [Fact q.Prime]
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (hreg : IsRegularLocalRing R) (hdim : ringKrullDim R = 2)
    (x₀ x₁ : R) (hmax : maximalIdeal R = Ideal.span {x₀, x₁})
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π})
    (g : W →+* R) [IsLocalHom g] (hres : ∀ r : R, ∃ w : W, r - g w ∈ maximalIdeal R)
    (F uF : R) (huF : IsUnit uF) (hπF : g π = uF * F)
    (hF : F - (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ maximalIdeal R ^ (q + 2)) :
    ∃ (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
      (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
      (e : R ≃+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C π * v - f * u}),
      (∀ w : W, e (g w) = Ideal.Quotient.mk _ (MvPowerSeries.C w)) ∧
      e x₀ = Ideal.Quotient.mk _ (MvPowerSeries.X 0) ∧ e x₁ = Ideal.Quotient.mk _ (MvPowerSeries.X 1) := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_eq_mul.solution
