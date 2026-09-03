import Mathlib
import Definitions.Def_ModularCurve_PeriodHomPair
import P2M.Util
import P2M.Sol.S_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem
    (Γ : Subgroup SL(2, ℤ)) (hΓ : ∀ γ ∈ Γ, ModularCurve.Period.jConjSL γ ∈ Γ) (k : ℤ)
    (f : CuspForm Γ k) :
    ∃ g : CuspForm Γ k, ∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ)) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem.solution
