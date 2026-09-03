import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_taylorShift_sum_C_mul_prod

set_option autoImplicit false

theorem PowerSeries.taylorShift_sum_C_mul_prod
    {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    {ι : Type*} (s : Finset ι) (c : ι → L) {κ : Type*} [Fintype κ] (F : ι → κ → PowerSeries L)
    {ρ : ℝ} (hρ : 0 < ρ) (hF : ∀ i ∈ s, ∀ j n, ‖PowerSeries.coeff n (F i j)‖ * ρ ^ n ≤ 1)
    (a : L) (ha : ‖a‖ < ρ) :
    (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) (∑ i ∈ s, PowerSeries.C (c i) * ∏ j, F i j) * ((n + k).choose n : L) * a ^ k)
      = ∑ i ∈ s, PowerSeries.C (c i) * ∏ j, (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) (F i j) * ((n + k).choose n : L) * a ^ k) := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_taylorShift_sum_C_mul_prod.solution
