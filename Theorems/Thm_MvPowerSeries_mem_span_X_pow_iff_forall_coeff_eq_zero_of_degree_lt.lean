import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt

set_option autoImplicit false

open IsLocalRing

theorem MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt
    (W : Type) [CommRing W] (e : ℕ) (g : MvPowerSeries (Fin 2) W) :
    g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e ↔
      ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < e → MvPowerSeries.coeff n g = 0 := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt.solution
