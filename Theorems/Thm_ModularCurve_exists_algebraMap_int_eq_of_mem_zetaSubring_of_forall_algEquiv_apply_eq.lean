import Mathlib
import Definitions.Def_ModularCurve_LevelFunctionField
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algebraMap_int_eq_of_mem_zetaSubring_of_forall_algEquiv_apply_eq

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_algebraMap_int_eq_of_mem_zetaSubring_of_forall_algEquiv_apply_eq
    (q : ℕ) [Fact q.Prime] (c : CyclotomicField q ℚ) (hc : c ∈ zetaSubring q)
    (hfix : ∀ σ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ, σ c = c) :
    ∃ m : ℤ, algebraMap ℤ (CyclotomicField q ℚ) m = c := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algebraMap_int_eq_of_mem_zetaSubring_of_forall_algEquiv_apply_eq.solution
