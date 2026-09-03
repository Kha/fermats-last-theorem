import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import P2M.Util
import P2M.Sol.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_hasCharConductor_of_ratio
attribute [-instance] FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete FLT.SpectralSide.instCompactSpaceMatrix
attribute [-simp] FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv

theorem LocalNewvector.PSCarrier.isIrreducibleGLRep_of_hasCharConductor_of_ratio (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {c₁ c₂ : ℕ} (hc₁ : LocalNewvector.HasCharConductor p μ₁ c₁) (hc₂ : LocalNewvector.HasCharConductor p μ₂ c₂)
    (hγ : LocalNewvector.IsUnramified p (μ₁⁻¹ * μ₂) →
      (μ₁ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ) * ((μ₂ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ))⁻¹ ≠ (p : ℂ) ∧
      (μ₁ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ) * ((μ₂ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ))⁻¹ ≠ ((p : ℂ))⁻¹) :
    LocalNewvector.IsIrreducibleGLRep p (LocalNewvector.PSCarrier p μ₁ μ₂) := by p2m_exact_reverting @_root_.P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_hasCharConductor_of_ratio.solution
