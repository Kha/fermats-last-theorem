import Mathlib
import P2M.Util
import P2M.Sol.S_ContinuousLinearMap_eq_zero_of_forall_exists_mem_sub_real_smul_eq

set_option autoImplicit false

open scoped InnerProductSpace

theorem ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (E : Submodule ℂ H)
    (hsym : ∀ x ∈ E, ∀ y ∈ E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (v : H) (hsurj : ∀ c : ℝ, ∃ w ∈ E, T w - (c : ℂ) • w = v) :
    v = 0 := by p2m_exact_reverting @_root_.P2MW.S_ContinuousLinearMap_eq_zero_of_forall_exists_mem_sub_real_smul_eq.solution
