import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_CuspForm_exists_ne_zero_forall_natCast_mul_qCoeff_mem_bot_of_forall_qCoeff_mem_range

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_ne_zero_forall_natCast_mul_qCoeff_mem_bot_of_forall_qCoeff_mem_range
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (f : CuspForm (CohCarrier.GammaH M H) k)
    (hf : ∀ n : ℕ, ModularFormClass.qCoeff (⇑f) n ∈ (algebraMap ℚ ℂ).range) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ n : ℕ, (D : ℂ) * ModularFormClass.qCoeff (⇑f) n ∈ (⊥ : Subring ℂ) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_ne_zero_forall_natCast_mul_qCoeff_mem_bot_of_forall_qCoeff_mem_range.solution
