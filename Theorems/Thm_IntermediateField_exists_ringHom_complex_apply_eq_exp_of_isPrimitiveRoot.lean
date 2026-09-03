import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_exists_ringHom_complex_apply_eq_exp_of_isPrimitiveRoot

set_option autoImplicit false

theorem IntermediateField.exists_ringHom_complex_apply_eq_exp_of_isPrimitiveRoot
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (q : ℕ) [NeZero q]
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ q) :
    ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_exists_ringHom_complex_apply_eq_exp_of_isPrimitiveRoot.solution
