import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_iDeg_comp

set_option autoImplicit false

theorem CohCarrier.iDeg_comp {M₁ M₂ M₃ d₁ d₂ : ℕ} {H₁ : Subgroup (ZMod M₁)ˣ} {H₂ : Subgroup (ZMod M₂)ˣ}
    {H₃ : Subgroup (ZMod M₃)ˣ} {A : Type*} [AddCommGroup A]
    [NeZero M₂] [NeZero M₃] [NeZero d₁] [NeZero d₂] [NeZero (d₁ * d₂)]
    (h₁₂ : LevelLE M₁ M₂ H₁ H₂ d₁) (h₂₃ : LevelLE M₂ M₃ H₂ H₃ d₂)
    (h₁₃ : LevelLE M₁ M₃ H₁ H₃ (d₁ * d₂)) (φ : H1 M₁ H₁ A) :
    iDeg' M₁ M₃ H₁ H₃ (d₁ * d₂) A h₁₃ φ
      = iDeg' M₂ M₃ H₂ H₃ d₂ A h₂₃ (iDeg' M₁ M₂ H₁ H₂ d₁ A h₁₂ φ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_iDeg_comp.solution
