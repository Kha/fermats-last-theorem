import Definitions.Def_LanglandsTunnell_ArchBaseChange
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_prod_twistedGammaR_mul_prod_twistedGammaC_archOfParam_eq_archFactor_mul_of_principal

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.prod_twistedGammaR_mul_prod_twistedGammaC_archOfParam_eq_archFactor_mul_of_principal
    (K : Type) [Field K] [NumberField K]
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
    (P : RealArchParam) (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2) (hP : P = RealArchParam.principal ν₁ a₁ ν₂ a₂)
    (s : ℂ) :
    ((twistedGammaR K (archOfParamR K P) uR aR).map fun x => Complex.Gammaℝ (s + x)).prod *
        ((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map
          fun x => Complex.Gammaℂ (s + x)).prod =
      (P.twist (uR w₀ h₀) (aR w₀ h₀)).archFactor s *
        ((P₂.twist ν₁ a₁).archFactor s * (P₂.twist ν₂ a₂).archFactor s) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_prod_twistedGammaR_mul_prod_twistedGammaC_archOfParam_eq_archFactor_mul_of_principal.solution
