import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_powerSeries_algEquiv_apply_X_eq_of_maximalIdeal_eq_span_pair_of_ringKrullDim_eq_two

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_powerSeries_algEquiv_apply_X_eq_of_maximalIdeal_eq_span_pair_of_ringKrullDim_eq_two
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀] [IsAdicComplete (maximalIdeal W₀) W₀]
    (ϖ : W₀) (hϖ : maximalIdeal W₀ = Ideal.span {ϖ})
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra W₀ R] (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap W₀ R)))
    (y : R) (h𝔪 : maximalIdeal R = Ideal.span {algebraMap W₀ R ϖ, y})
    (hdim : ringKrullDim R = 2) :
    ∃ e : PowerSeries W₀ ≃ₐ[W₀] R, e PowerSeries.X = y := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_powerSeries_algEquiv_apply_X_eq_of_maximalIdeal_eq_span_pair_of_ringKrullDim_eq_two.solution
