import Definitions.Def_LanglandsTunnell_ArchParam
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RealArchParam_eq_of_archFactor_twist_mul_eq_archFactor_twist_mul_entire

set_option autoImplicit false

open Complex

theorem LanglandsTunnell.RealArchParam.eq_of_archFactor_twist_mul_eq_archFactor_twist_mul_entire
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂) (htype : |(u₁ - u₂).re| < 1)
    (P' : RealArchParam) (hP' : P' = .principal u₁ a₁ u₂ a₂ ∨ P' = .principal u₁ a₂ u₂ a₁)
    (ρ : ℂ) (hρ : ρ ≠ 0) (Φ : ℂ → ℂ) (hΦ : Differentiable ℂ Φ) (σ₀ : ℝ)
    (h : ∀ s : ℂ, σ₀ < s.re →
      ρ * (P'.twist 0 0).archFactor s = ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 0).archFactor s * Φ s) :
    P' = .principal u₁ a₁ u₂ a₂ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RealArchParam_eq_of_archFactor_twist_mul_eq_archFactor_twist_mul_entire.solution
