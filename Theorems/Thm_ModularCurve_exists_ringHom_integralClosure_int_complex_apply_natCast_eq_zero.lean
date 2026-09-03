import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_ringHom_integralClosure_int_complex_apply_natCast_eq_zero

set_option autoImplicit false

theorem ModularCurve.exists_ringHom_integralClosure_int_complex_apply_natCast_eq_zero
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ φ : ↥(integralClosure ℤ ℂ) →+* K, φ (p : ↥(integralClosure ℤ ℂ)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_ringHom_integralClosure_int_complex_apply_natCast_eq_zero.solution
