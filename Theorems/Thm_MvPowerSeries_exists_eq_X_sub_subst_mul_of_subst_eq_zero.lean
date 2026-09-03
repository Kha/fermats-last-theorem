import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_eq_X_sub_subst_mul_of_subst_eq_zero

set_option autoImplicit false

universe u

open MvPowerSeries

theorem MvPowerSeries.exists_eq_X_sub_subst_mul_of_subst_eq_zero
    {R : Type u} [CommRing R] (f : MvPowerSeries (Fin 2) R)
    (φ : PowerSeries R) (hφ0 : PowerSeries.constantCoeff φ = 0)
    (hroot : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), φ] f = 0) :
    ∃ M : MvPowerSeries (Fin 2) R,
      f = (X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) φ) * M := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_eq_X_sub_subst_mul_of_subst_eq_zero.solution
