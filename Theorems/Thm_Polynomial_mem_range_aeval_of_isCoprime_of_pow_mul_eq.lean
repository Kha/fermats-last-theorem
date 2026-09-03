import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_mem_range_aeval_of_isCoprime_of_pow_mul_eq
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

theorem Polynomial.mem_range_aeval_of_isCoprime_of_pow_mul_eq
    {F A : Type*} [Field F] [CommRing A] [IsDomain A] [Algebra F A]
    (x : A) (hx : Transcendental F x) {f g : Polynomial F} (hfg : IsCoprime f g) (z : A) (m n : ℕ)
    (P Q : Polynomial F) (hf : Polynomial.aeval x f ^ m * z = Polynomial.aeval x P)
    (hg : Polynomial.aeval x g ^ n * z = Polynomial.aeval x Q) :
    z ∈ (Polynomial.aeval (R := F) x).range := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_mem_range_aeval_of_isCoprime_of_pow_mul_eq.solution
