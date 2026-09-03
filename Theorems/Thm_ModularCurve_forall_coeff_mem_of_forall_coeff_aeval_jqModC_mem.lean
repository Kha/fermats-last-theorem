import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_forall_coeff_mem_of_forall_coeff_aeval_jqModC_mem

set_option autoImplicit false

theorem ModularCurve.forall_coeff_mem_of_forall_coeff_aeval_jqModC_mem
    {L : Type*} [Field L] (R : Subring L) (P : Polynomial L)
    (h : ∀ n : ℤ, (Polynomial.aeval (ModularCurve.jqModC L) P).coeff n ∈ R) :
    (∀ i : ℕ, P.coeff i ∈ R) ∧
      (P ≠ 0 → (Polynomial.aeval (ModularCurve.jqModC L) P).order = -(P.natDegree : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_forall_coeff_mem_of_forall_coeff_aeval_jqModC_mem.solution
