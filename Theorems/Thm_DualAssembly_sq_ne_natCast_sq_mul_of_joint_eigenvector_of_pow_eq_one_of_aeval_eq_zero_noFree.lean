import Mathlib
import P2M.Util
import P2M.Sol.S_DualAssembly_sq_ne_natCast_sq_mul_of_joint_eigenvector_of_pow_eq_one_of_aeval_eq_zero_noFree

set_option autoImplicit false

open scoped TensorProduct

theorem DualAssembly.sq_ne_natCast_sq_mul_of_joint_eigenvector_of_pow_eq_one_of_aeval_eq_zero_noFree
    (p : ℕ) [Fact p.Prime] {T : Type*} [AddCommGroup T] [Module ℤ_[p] T]
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] [Algebra ℤ_[p] K]
    (A D : Module.End ℤ_[p] T) (m : ℕ) (hm : 0 < m) (hD : D ^ m = 1)
    (c : ℕ) (P : Polynomial ℤ) (hPm : P.Monic) (hPA : Polynomial.aeval A P = 0)
    (hroots : ∀ z : ℂ, Polynomial.aeval z P = 0 → ‖z‖ < c)
    (v : K ⊗[ℤ_[p]] T) (a e : K) (hv : v ≠ 0)
    (hA : A.baseChange K v = a • v) (hDv : D.baseChange K v = e • v) :
    a ^ 2 ≠ (algebraMap ℤ_[p] K ((c : ℕ) : ℤ_[p])) ^ 2 * e := by p2m_exact_reverting @_root_.P2MW.S_DualAssembly_sq_ne_natCast_sq_mul_of_joint_eigenvector_of_pow_eq_one_of_aeval_eq_zero_noFree.solution
