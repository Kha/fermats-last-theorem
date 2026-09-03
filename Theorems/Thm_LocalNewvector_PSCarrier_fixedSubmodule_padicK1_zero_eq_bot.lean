import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import P2M.Util
import P2M.Sol.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot
attribute [-instance] FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete FLT.SpectralSide.instCompactSpaceMatrix
attribute [-simp] FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv

theorem LocalNewvector.PSCarrier.fixedSubmodule_padicK1_zero_eq_bot (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    (hram : ¬ LocalNewvector.IsUnramified p μ₁ ∨ ¬ LocalNewvector.IsUnramified p μ₂) :
    LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p 0) (LocalNewvector.PSCarrier p μ₁ μ₂) = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot.solution
