import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X

theorem MvPowerSeries.exists_rename_swap_eq_add_mul_X {W : Type*} [CommRing W] (f : MvPowerSeries (Fin 2) W) : ∃ A B : MvPowerSeries (Fin 2) W, MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) A = A ∧ MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) B = B ∧ f = A + B * MvPowerSeries.X 0 := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.solution
