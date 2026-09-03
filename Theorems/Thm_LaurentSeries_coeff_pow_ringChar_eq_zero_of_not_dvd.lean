import Mathlib
import P2M.Util
import P2M.Sol.S_LaurentSeries_coeff_pow_ringChar_eq_zero_of_not_dvd

universe u

theorem LaurentSeries.coeff_pow_ringChar_eq_zero_of_not_dvd
    {K : Type u} [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
    (g : LaurentSeries K) (n : ℤ) (hn : ¬ (ℓ : ℤ) ∣ n) :
    (g ^ ℓ).coeff n = 0 := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_coeff_pow_ringChar_eq_zero_of_not_dvd.solution
