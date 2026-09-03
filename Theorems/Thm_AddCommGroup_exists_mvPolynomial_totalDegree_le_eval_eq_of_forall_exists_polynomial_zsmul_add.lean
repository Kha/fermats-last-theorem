import Mathlib
import P2M.Util
import P2M.Sol.S_AddCommGroup_exists_mvPolynomial_totalDegree_le_eval_eq_of_forall_exists_polynomial_zsmul_add

set_option autoImplicit false

theorem AddCommGroup.exists_mvPolynomial_totalDegree_le_eval_eq_of_forall_exists_polynomial_zsmul_add
    {M : Type*} [AddCommGroup M] {R : Type*} [Field R] [CharZero R] (f : M → R) (d : ℕ)
    (hf : ∀ x y : M, ∃ p : Polynomial R, p.natDegree ≤ d ∧
      ∀ n : ℤ, f (n • x + y) = p.eval (n : R))
    {ι : Type*} [Fintype ι] (e : ι → M) :
    ∃ P : MvPolynomial ι R, P.totalDegree ≤ d ∧
      ∀ c : ι → ℤ, MvPolynomial.eval (fun i => (c i : R)) P = f (∑ i, c i • e i) := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_exists_mvPolynomial_totalDegree_le_eval_eq_of_forall_exists_polynomial_zsmul_add.solution
