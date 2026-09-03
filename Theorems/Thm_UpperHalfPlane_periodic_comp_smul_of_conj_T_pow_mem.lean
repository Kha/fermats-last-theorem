import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_periodic_comp_smul_of_conj_T_pow_mem

open scoped UpperHalfPlane MatrixGroups

theorem UpperHalfPlane.periodic_comp_smul_of_conj_T_pow_mem {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}
    (hF : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) {σ : SL(2, ℤ)} {h : ℕ}
    (hσ : σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ) :
    Function.Periodic (fun z : ℂ => F (σ • UpperHalfPlane.ofComplex z)) h := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_periodic_comp_smul_of_conj_T_pow_mem.solution
