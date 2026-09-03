import Definitions.Def_LanglandsTunnell_HeckeTate
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_heckeDatum_archFactorDual_eq_archFactor_dual_twist_mul_GammaR

set_option autoImplicit false

open NumberField

theorem LanglandsTunnell.CubicInduction.heckeDatum_archFactorDual_eq_archFactor_dual_twist_mul_GammaR
    (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (t : ℂ) (e : ℤ) (s : ℂ) :
    (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
        (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual s =
      ((P₂.twist t (e : ZMod 2)).dual).archFactor s *
        Complex.Gammaℝ (s + (-(uR w₀ h₀ + t) + LanglandsTunnell.signShift (aR w₀ h₀ + (e : ZMod 2)))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_heckeDatum_archFactorDual_eq_archFactor_dual_twist_mul_GammaR.solution
