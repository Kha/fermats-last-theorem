import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_norm_coeff_sum_C_mul_prod_mul_pow_le

set_option autoImplicit false

theorem PowerSeries.norm_coeff_sum_C_mul_prod_mul_pow_le
    {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    {ι : Type*} (s : Finset ι) (c : ι → L) {κ : Type*} [Fintype κ] (F : ι → κ → PowerSeries L)
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hF : ∀ i ∈ s, ∀ j n, ‖PowerSeries.coeff n (F i j)‖ * ρ ^ n ≤ 1) (hc : ∀ i ∈ s, ‖c i‖ ≤ B)
    (n : ℕ) :
    ‖PowerSeries.coeff n (∑ i ∈ s, PowerSeries.C (c i) * ∏ j, F i j)‖ * ρ ^ n ≤ B := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_norm_coeff_sum_C_mul_prod_mul_pow_le.solution
