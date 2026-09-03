import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_notMem_forall_smul_eq_zero_of_isMaximal_of_forall_smul_eq_zero_imp

set_option autoImplicit false

theorem Module.exists_notMem_forall_smul_eq_zero_of_isMaximal_of_forall_smul_eq_zero_imp
    {T : Type*} [CommRing T] {M : Type*} [AddCommGroup M] [Module T M] [Finite M]
    (𝔓 : Ideal T) (h𝔓 : 𝔓.IsMaximal)
    (hno : ∀ x : M, (∀ a ∈ 𝔓, a • x = 0) → x = 0) :
    ∃ s : T, s ∉ 𝔓 ∧ ∀ x : M, s • x = 0 := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_notMem_forall_smul_eq_zero_of_isMaximal_of_forall_smul_eq_zero_imp.solution
