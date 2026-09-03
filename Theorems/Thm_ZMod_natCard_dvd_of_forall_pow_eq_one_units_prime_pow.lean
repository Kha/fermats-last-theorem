import Mathlib
import P2M.Util
import P2M.Sol.S_ZMod_natCard_dvd_of_forall_pow_eq_one_units_prime_pow

theorem ZMod.natCard_dvd_of_forall_pow_eq_one_units_prime_pow
    (p : ℕ) (hp : p.Prime) (q : ℕ) (hq : q ≠ 0)
    (H : Subgroup (ZMod (p ^ (padicValNat p q + 1)))ˣ) (hH : ∀ x ∈ H, x ^ q = 1) :
    Nat.card H ∣ q := by p2m_exact_reverting @_root_.P2MW.S_ZMod_natCard_dvd_of_forall_pow_eq_one_units_prime_pow.solution
