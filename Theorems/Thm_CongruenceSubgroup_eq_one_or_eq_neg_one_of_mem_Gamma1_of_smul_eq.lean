import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_eq_one_or_eq_neg_one_of_mem_Gamma1_of_smul_eq

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.eq_one_or_eq_neg_one_of_mem_Gamma1_of_smul_eq (M : ℕ) (hM : 4 ≤ M)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 M ∨ -γ ∈ CongruenceSubgroup.Gamma1 M)
    (τ : UpperHalfPlane) (hτ : γ • τ = τ) : γ = 1 ∨ γ = -1 := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_eq_one_or_eq_neg_one_of_mem_Gamma1_of_smul_eq.solution
