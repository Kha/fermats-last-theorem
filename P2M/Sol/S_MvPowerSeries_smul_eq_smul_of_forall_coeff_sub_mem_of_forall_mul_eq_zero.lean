import Mathlib
import P2M.Util
namespace P2MW.S_MvPowerSeries_smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero

set_option autoImplicit false

universe u w

theorem solution
    {R : Type u} [CommRing R] {τ : Type w} (M : Ideal R) (j : R) (hj : ∀ m ∈ M, m * j = 0)
    (g g' : MvPowerSeries τ R) (h : ∀ n, MvPowerSeries.coeff n g - MvPowerSeries.coeff n g' ∈ M) :
    j • g = j • g' := by
  refine MvPowerSeries.ext fun n => ?_
  rw [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul]
  have h0 : (MvPowerSeries.coeff n g - MvPowerSeries.coeff n g') * j = 0 := hj _ (h n)
  rw [sub_mul, sub_eq_zero] at h0
  rw [mul_comm, h0, mul_comm]
