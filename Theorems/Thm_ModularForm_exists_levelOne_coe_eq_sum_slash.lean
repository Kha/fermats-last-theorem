import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_exists_levelOne_coe_eq_sum_slash

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem ModularForm.exists_levelOne_coe_eq_sum_slash
    (Γ : Subgroup SL(2, ℤ)) {k : ℤ} (hk : Even k)
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (s : Finset SL(2, ℤ))
    (hcover : ∀ g : SL(2, ℤ), ∃ x ∈ s, g * x⁻¹ ∈ Γ ∨ -(g * x⁻¹) ∈ Γ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, (x * y⁻¹ ∈ Γ ∨ -(x * y⁻¹) ∈ Γ) → x = y) :
    ∃ F : ModularForm 𝒮ℒ k,
      (⇑F : UpperHalfPlane → ℂ) = ∑ x ∈ s, ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((x : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_levelOne_coe_eq_sum_slash.solution
