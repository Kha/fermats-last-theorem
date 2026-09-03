import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_tmul_one_sub_one_tmul_eq_sum_mul

set_option autoImplicit false

open scoped TensorProduct

theorem MvPolynomial.exists_tmul_one_sub_one_tmul_eq_sum_mul
    (R : Type*) [CommRing R] {m : ℕ} (g : MvPolynomial (Fin m) R) :
    ∃ a : Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R,
      g ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] g =
        ∑ j, a j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_tmul_one_sub_one_tmul_eq_sum_mul.solution
