import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpFunctionFieldC_eq_of_le_of_forall_mem_or_neg_mem

set_option autoImplicit false

theorem ModularCurve.qExpFunctionFieldC_eq_of_le_of_forall_mem_or_neg_mem
    (K : Type*) [Field K] {Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} (hle : Γ' ≤ Γ)
    (hT : ModularGroup.T ∈ Γ') (hpm : ∀ γ ∈ Γ, γ ∈ Γ' ∨ -γ ∈ Γ') :
    ModularCurve.qExpFunctionFieldC K Γ' = ModularCurve.qExpFunctionFieldC K Γ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpFunctionFieldC_eq_of_le_of_forall_mem_or_neg_mem.solution
