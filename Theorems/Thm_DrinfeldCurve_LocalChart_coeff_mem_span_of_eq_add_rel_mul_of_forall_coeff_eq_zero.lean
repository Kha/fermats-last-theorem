import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero

set_option autoImplicit false

open IsLocalRing

theorem DrinfeldCurve.LocalChart.coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero
    (W : Type) [CommRing W] [IsDomain W] (π : W) (hπ : π ≠ 0)
    (f u v : MvPowerSeries (Fin 2) W) (hv : IsUnit v) (hf : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) f = 0)
    (e : ℕ) (g g₁ r : MvPowerSeries (Fin 2) W)
    (hg : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < e → MvPowerSeries.coeff n g = 0)
    (hg₁ : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < e + 1 → MvPowerSeries.coeff n g₁ = 0)
    (hrel : g = g₁ + (MvPowerSeries.C π * v - f * u) * r)
    (n : Fin 2 →₀ ℕ) (hn : n 0 + n 1 = e) :
    MvPowerSeries.coeff n g ∈ Ideal.span {π} := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero.solution
