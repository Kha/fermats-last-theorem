import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_exists_ringHom_forall_apply_eq_mk_C_of_apply_eq_mk_C_of_forall_pow_pow_eq

set_option autoImplicit false

open IsLocalRing

theorem DrinfeldCurve.LocalChart.exists_ringHom_forall_apply_eq_mk_C_of_apply_eq_mk_C_of_forall_pow_pow_eq
    (q : ℕ) [Fact q.Prime]
    (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁] [IsAdicComplete (maximalIdeal W₁) W₁]
    (π₁ : W₁) (hπ₁ : maximalIdeal W₁ = Ideal.span {π₁})
    (halg : ∀ x : ResidueField W₁, ∃ n : ℕ, 1 ≤ n ∧ x ^ (q ^ n) = x)
    (W₂ : Type) [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂] [IsAdicComplete (maximalIdeal W₂) W₂]
    (π₂ : W₂) (hπ₂ : maximalIdeal W₂ = Ideal.span {π₂}) (hq₂ : (q : W₂) ∈ maximalIdeal W₂)
    (f₂ u₂ v₂ : MvPowerSeries (Fin 2) W₂) (hu₂ : IsUnit u₂) (hv₂ : IsUnit v₂)
    (hf₂ : f₂ - DrinfeldCurve.LocalChart.drinfeldForm q W₂ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₂), MvPowerSeries.X 1}) ^ (q + 2))
    (θ : W₁ →+* MvPowerSeries (Fin 2) W₂ ⧸ Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂})
    (hθ : θ π₁ = Ideal.Quotient.mk _ (MvPowerSeries.C π₂)) :
    ∃ ρ : W₁ →+* W₂, ρ π₁ = π₂ ∧
      ∀ w : W₁, θ w = Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂}) (MvPowerSeries.C (ρ w)) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_exists_ringHom_forall_apply_eq_mk_C_of_apply_eq_mk_C_of_forall_pow_pow_eq.solution
