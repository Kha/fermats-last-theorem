import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_norm_algebraNorm_eq_pow_finrank_padic

set_option autoImplicit false
open IntermediateField
theorem IntermediateField.norm_algebraNorm_eq_pow_finrank_padic (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (L : IntermediateField K (PadicAlgCl q)) [FiniteDimensional K L] (w : L) :
    ‖((Algebra.norm K w : K) : PadicAlgCl q)‖ = ‖(w : PadicAlgCl q)‖ ^ Module.finrank K L := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_norm_algebraNorm_eq_pow_finrank_padic.solution
