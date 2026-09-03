import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero

set_option autoImplicit false

universe u w
theorem MvPowerSeries.smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero
    {R : Type u} [CommRing R] {τ : Type w} (M : Ideal R) (j : R) (hj : ∀ m ∈ M, m * j = 0)
    (g g' : MvPowerSeries τ R) (h : ∀ n, MvPowerSeries.coeff n g - MvPowerSeries.coeff n g' ∈ M) :
    j • g = j • g' := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero.solution
