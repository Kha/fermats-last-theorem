import Mathlib
import P2M.Util
import P2M.Sol.S_PadicAlgCl_exists_forall_exists_polynomial_aeval_eq_of_norm_le_one

set_option autoImplicit false

theorem PadicAlgCl.exists_forall_exists_polynomial_aeval_eq_of_norm_le_one
    (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F]
    (E : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F E] :
    ∃ x : E, ‖(x : PadicAlgCl p)‖ ≤ 1 ∧ IntermediateField.adjoin F {x} = ⊤ ∧
      ∀ y : E, ‖(y : PadicAlgCl p)‖ ≤ 1 →
        ∃ P : Polynomial ℚ_[p], (∀ i, ‖P.coeff i‖ ≤ 1) ∧ Polynomial.aeval x P = y := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_exists_forall_exists_polynomial_aeval_eq_of_norm_le_one.solution
