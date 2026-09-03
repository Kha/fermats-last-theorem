import Mathlib
import P2M.Util
import P2M.Sol.S_PadicAlgCl_norm_mul_aeval_derivative_minpoly_le_one_of_forall_norm_trace_mul_le_one

set_option autoImplicit false

theorem PadicAlgCl.norm_mul_aeval_derivative_minpoly_le_one_of_forall_norm_trace_mul_le_one
    (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F]
    (E : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F E] {α : E}
    (hα : ‖(α : PadicAlgCl p)‖ ≤ 1) (hgen : IntermediateField.adjoin F {α} = ⊤) (z : E)
    (hz : ∀ w : E, ‖(w : PadicAlgCl p)‖ ≤ 1 →
      ‖((Algebra.trace F E (z * w) : F) : PadicAlgCl p)‖ ≤ 1) :
    ‖((z * Polynomial.aeval α (Polynomial.derivative (minpoly F α)) : E) : PadicAlgCl p)‖ ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_norm_mul_aeval_derivative_minpoly_le_one_of_forall_norm_trace_mul_le_one.solution
