import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_powerSeries_subst_eq_zero_of_sub_drinfeld_mem_pow

set_option autoImplicit false

open MvPowerSeries

theorem MvPowerSeries.exists_powerSeries_subst_eq_zero_of_sub_drinfeld_mem_pow
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] (hq : (q : k) = 0)
    (f : MvPowerSeries (Fin 2) k)
    (hf : f - (X 0 * X 1 ^ q - X 0 ^ q * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) k), X 1}) ^ (q + 2))
    (a : k) (ha : a ^ q = a) :
    ∃ φ : PowerSeries k,
      PowerSeries.constantCoeff φ = 0 ∧ PowerSeries.coeff 1 φ = a ∧
      MvPowerSeries.subst ![(PowerSeries.X : PowerSeries k), φ] f = 0 := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_powerSeries_subst_eq_zero_of_sub_drinfeld_mem_pow.solution
