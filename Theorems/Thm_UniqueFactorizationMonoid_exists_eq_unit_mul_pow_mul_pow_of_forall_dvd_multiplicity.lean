import Mathlib
import P2M.Util
import P2M.Sol.S_UniqueFactorizationMonoid_exists_eq_unit_mul_pow_mul_pow_of_forall_dvd_multiplicity

set_option autoImplicit false

open IsLocalRing Polynomial

theorem UniqueFactorizationMonoid.exists_eq_unit_mul_pow_mul_pow_of_forall_dvd_multiplicity
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (s : R) (hs : Prime s) (e : ℕ) (he : 0 < e) (f : R) (hf : f ≠ 0)
    (hdiv : ∀ p : R, Prime p → ¬ Associated p s → e ∣ multiplicity p f) :
    ∃ (w : Rˣ) (k : ℕ) (g : R), f = (w : R) * s ^ k * g ^ e := by p2m_exact_reverting @_root_.P2MW.S_UniqueFactorizationMonoid_exists_eq_unit_mul_pow_mul_pow_of_forall_dvd_multiplicity.solution
