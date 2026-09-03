import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_exists_algEquiv_mvPowerSeries_quotient_span_C_sub_of_maximalIdeal_eq_span_pair
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open IsLocalRing MvPowerSeries

theorem IsRegularLocalRing.exists_algEquiv_mvPowerSeries_quotient_span_C_sub_of_maximalIdeal_eq_span_pair
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    (π : W₀) (hπ : maximalIdeal W₀ = Ideal.span {π})
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra W₀ R]
    [IsAdicComplete (maximalIdeal R) R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2)
    (hres : ∀ r : R, ∃ w : W₀, r - algebraMap W₀ R w ∈ maximalIdeal R)
    (hπR : algebraMap W₀ R π ∈ maximalIdeal R)
    (x₀ x₁ : R) (hmax : maximalIdeal R = Ideal.span {x₀, x₁}) :
    ∃ (h : MvPowerSeries (Fin 2) W₀) (_ : MvPowerSeries.constantCoeff h = 0)
      (e : R ≃ₐ[W₀] (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C π - h})),
      e x₀ = Ideal.Quotient.mk _ (MvPowerSeries.X 0) ∧ e x₁ = Ideal.Quotient.mk _ (MvPowerSeries.X 1) := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_exists_algEquiv_mvPowerSeries_quotient_span_C_sub_of_maximalIdeal_eq_span_pair.solution
