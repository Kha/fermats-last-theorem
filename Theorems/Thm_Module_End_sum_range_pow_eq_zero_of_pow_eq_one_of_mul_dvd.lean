import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_sum_range_pow_eq_zero_of_pow_eq_one_of_mul_dvd

set_option autoImplicit false
theorem Module.End.sum_range_pow_eq_zero_of_pow_eq_one_of_mul_dvd {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (p : ℕ) [CharP R p] (T : Module.End R V) {d n : ℕ} (hd : T ^ d = 1) (hdn : p * d ∣ n) :
    ∑ i ∈ Finset.range n, T ^ i = 0 := by p2m_exact_reverting @_root_.P2MW.S_Module_End_sum_range_pow_eq_zero_of_pow_eq_one_of_mul_dvd.solution
