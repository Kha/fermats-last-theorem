import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_exists_isPrincipal_degree_eq_zero_forall_mem_support_add_of_surgery

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.exists_isPrincipal_degree_eq_zero_forall_mem_support_add_of_surgery
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (good : Place K F → Prop)
    (surgery : ∀ V₀ : Place K F, ¬ good V₀ →
      ∃ p : Divisor K F, Divisor.IsPrincipal p ∧ p V₀ = -1 ∧ Divisor.degree p = 0 ∧
        ∀ V ∈ p.support, V ≠ V₀ → good V)
    (D : Divisor K F) :
    ∃ e : Divisor K F, Divisor.IsPrincipal e ∧ Divisor.degree e = 0 ∧
      ∀ V ∈ (D + e).support, good V := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_exists_isPrincipal_degree_eq_zero_forall_mem_support_add_of_surgery.solution
