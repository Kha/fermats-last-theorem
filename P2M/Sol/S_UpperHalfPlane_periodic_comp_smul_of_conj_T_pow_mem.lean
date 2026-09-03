import Mathlib
import P2M.Util
namespace P2MW.S_UpperHalfPlane_periodic_comp_smul_of_conj_T_pow_mem

open scoped UpperHalfPlane MatrixGroups

theorem solution {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}
    (hF : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) {σ : SL(2, ℤ)} {h : ℕ}
    (hσ : σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ) :
    Function.Periodic (fun z : ℂ => F (σ • UpperHalfPlane.ofComplex z)) h := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + h).im := by simpa using hw
    simp only [UpperHalfPlane.ofComplex_apply_of_im_pos hw',
      UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    have key : (⟨w + h, hw'⟩ : ℍ) = ModularGroup.T ^ h • (⟨w, hw⟩ : ℍ) := by
      apply UpperHalfPlane.ext
      rw [← zpow_natCast, ModularGroup.coe_T_zpow_smul_eq]
      simp
    have := hF _ hσ (σ • (⟨w, hw⟩ : ℍ))
    rw [mul_smul, mul_smul, inv_smul_smul] at this
    rw [key]
    exact this
  · have hw' : (w + h).im ≤ 0 := by simpa using hw
    simp only [UpperHalfPlane.ofComplex_apply_of_im_nonpos hw',
      UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hw)]
