import Mathlib
import P2M.Util
import P2M.Sol.S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le

set_option autoImplicit false

theorem PadicAlgCl.exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le
    (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F]
    (E : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F E] (r : ℝ)
    (hE : ∀ z : E, (∀ w : E, ‖(w : PadicAlgCl p)‖ ≤ 1 →
        ‖((Algebra.trace F E (z * w) : F) : PadicAlgCl p)‖ ≤ 1) → ‖(z : PadicAlgCl p)‖ ≤ r)
    (x : F) (hx : ‖(x : PadicAlgCl p)‖ ≤ r⁻¹) :
    ∃ y : E, ‖(y : PadicAlgCl p)‖ ≤ 1 ∧ Algebra.trace F E y = x := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le.solution
