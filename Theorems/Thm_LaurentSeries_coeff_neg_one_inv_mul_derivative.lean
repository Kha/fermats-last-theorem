module

public import Mathlib
import P2M.Util
import P2M.Sol.S_LaurentSeries_coeff_neg_one_inv_mul_derivative

@[expose] public section
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

theorem LaurentSeries.coeff_neg_one_inv_mul_derivative {R : Type*} [CommRing R]
    (f g : LaurentSeries R) (k : ℤ) (hk : f.coeff k = 1) (hlt : ∀ n < k, f.coeff n = 0)
    (hinv : f * g = 1) :
    (g * LaurentSeries.derivative R f).coeff (-1) = (k : R) := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_coeff_neg_one_inv_mul_derivative.solution
