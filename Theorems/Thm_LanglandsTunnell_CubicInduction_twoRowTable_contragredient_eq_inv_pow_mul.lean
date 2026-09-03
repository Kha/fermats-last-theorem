import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_twoRowTable_contragredient_eq_inv_pow_mul

set_option autoImplicit false

open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.twoRowTable_contragredient_eq_inv_pow_mul
    (e₁ e₂ e₃ : ℂ) (he₃ : e₃ ≠ 0)
    (h : ℕ → ℂ) (hh0 : h 0 = 1) (hh1 : h 1 = e₁) (hh2 : h 2 = e₁ ^ 2 - e₂)
    (hh3 : ∀ n : ℕ, h (n + 3) = e₁ * h (n + 2) - e₂ * h (n + 1) + e₃ * h n)
    (hd : ℕ → ℂ) (hhd0 : hd 0 = 1) (hhd1 : hd 1 = e₂ * e₃⁻¹) (hhd2 : hd 2 = (e₂ * e₃⁻¹) ^ 2 - e₁ * e₃⁻¹)
    (hhd3 : ∀ n : ℕ, hd (n + 3) = (e₂ * e₃⁻¹) * hd (n + 2) - (e₁ * e₃⁻¹) * hd (n + 1) + e₃⁻¹ * hd n)
    (u : ℕ → ℕ → ℂ) (hu0 : ∀ a : ℕ, u a 0 = h a)
    (hu1 : ∀ a b : ℕ, u a (b + 1) = h a * h (b + 1) - h (a + 1) * h b)
    (ud : ℕ → ℕ → ℂ) (hud0 : ∀ a : ℕ, ud a 0 = hd a)
    (hud1 : ∀ a b : ℕ, ud a (b + 1) = hd a * hd (b + 1) - hd (a + 1) * hd b)
    (k₁ k₂ : ℕ) (hk : k₂ ≤ k₁) :
    ud k₁ k₂ = e₃⁻¹ ^ k₁ * u k₁ (k₁ - k₂) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_twoRowTable_contragredient_eq_inv_pow_mul.solution
