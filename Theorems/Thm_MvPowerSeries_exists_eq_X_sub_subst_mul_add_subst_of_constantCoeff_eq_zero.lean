import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero

set_option autoImplicit false

open MvPowerSeries

theorem MvPowerSeries.exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero
    (k : Type*) [CommRing k] (φ : PowerSeries k) (hφ0 : PowerSeries.constantCoeff φ = 0)
    (G : MvPowerSeries (Fin 2) k) :
    ∃ Q : MvPowerSeries (Fin 2) k,
      G = (X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ) * Q +
        MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 2) k), PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ] G := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero.solution
