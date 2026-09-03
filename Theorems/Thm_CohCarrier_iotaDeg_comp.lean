import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_iotaDeg_comp

set_option autoImplicit false

theorem CohCarrier.iotaDeg_comp {M₁ M₂ M₃ d₁ d₂ : ℕ} {H₁ : Subgroup (ZMod M₁)ˣ} {H₂ : Subgroup (ZMod M₂)ˣ}
    {H₃ : Subgroup (ZMod M₃)ˣ}
    [NeZero M₂] [NeZero M₃] [NeZero d₁] [NeZero d₂] [NeZero (d₁ * d₂)]
    (h₁₂ : LevelLE M₁ M₂ H₁ H₂ d₁) (h₂₃ : LevelLE M₂ M₃ H₂ H₃ d₂)
    (h₁₃ : LevelLE M₁ M₃ H₁ H₃ (d₁ * d₂)) (γ : ↥(GammaH M₃ H₃)) :
    iotaDeg M₁ M₃ H₁ H₃ (d₁ * d₂) h₁₃ γ
      = iotaDeg M₁ M₂ H₁ H₂ d₁ h₁₂ (iotaDeg M₂ M₃ H₂ H₃ d₂ h₂₃ γ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_iotaDeg_comp.solution
