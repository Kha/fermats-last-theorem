import Mathlib
import P2M.Util
import P2M.Sol.S_AddSubgroup_exists_units_zmod_val_smul_eq_of_addOrderOf_eq_of_mem_zmultiples

set_option autoImplicit false

theorem AddSubgroup.exists_units_zmod_val_smul_eq_of_addOrderOf_eq_of_mem_zmultiples
    {G : Type*} [AddCommGroup G] (ℓ : ℕ) [NeZero ℓ] (P P' : G)
    (hP : addOrderOf P = ℓ) (hP' : addOrderOf P' = ℓ) (h : P' ∈ AddSubgroup.zmultiples P) :
    ∃ d : (ZMod ℓ)ˣ, P' = (d : ZMod ℓ).val • P := by p2m_exact_reverting @_root_.P2MW.S_AddSubgroup_exists_units_zmod_val_smul_eq_of_addOrderOf_eq_of_mem_zmultiples.solution
