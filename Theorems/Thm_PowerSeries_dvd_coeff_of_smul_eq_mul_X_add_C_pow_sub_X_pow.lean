import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow

set_option autoImplicit false

open IsLocalRing PowerSeries

theorem PowerSeries.dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow
    {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A]
    {n : ℕ} (hn : IsUnit (n : A)) {d e : A} (hd : d ∈ maximalIdeal A) (he : e ≠ 0)
    {u F : A⟦X⟧} (hF : e • F = u * (X + C d) ^ n - X ^ n) {j : ℕ} (hj : j + 2 ≤ n) :
    d ∣ coeff j F := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow.solution
