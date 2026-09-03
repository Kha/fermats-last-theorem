import Definitions.Def_LanglandsTunnell_ArchBaseChange
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_prod_map_GammaR_twistedGammaR_archOfParamR_principal_three_real

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.prod_map_GammaR_twistedGammaR_archOfParamR_principal_three_real
    (K : Type) [Field K] [NumberField K]
    (w₀ w₁ w₂ : NumberField.InfinitePlace K) (h₀ : w₀.IsReal) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal)
    (h01 : w₀ ≠ w₁) (h02 : w₀ ≠ w₂) (h12 : w₁ ≠ w₂)
    (hall : ∀ w : NumberField.InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂)
    (uR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℤ)
    (P : RealArchParam) (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2) (hP : P = RealArchParam.principal ν₁ a₁ ν₂ a₂)
    (s : ℂ) :
    (((twistedGammaR K (archOfParamR K P) uR aR).map fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod =
        (Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + uR w₀ h₀) + signShift (a₁ + aR w₀ h₀))) *
        Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + uR w₀ h₀) + signShift (a₂ + aR w₀ h₀)))) *
        ((Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + uR w₁ h₁) + signShift (a₁ + aR w₁ h₁))) *
        Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + uR w₁ h₁) + signShift (a₂ + aR w₁ h₁)))) *
        (Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + uR w₂ h₂) + signShift (a₁ + aR w₂ h₂))) *
        Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + uR w₂ h₂) + signShift (a₂ + aR w₂ h₂)))))) ∧
    (((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod = 1) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_prod_map_GammaR_twistedGammaR_archOfParamR_principal_three_real.solution
