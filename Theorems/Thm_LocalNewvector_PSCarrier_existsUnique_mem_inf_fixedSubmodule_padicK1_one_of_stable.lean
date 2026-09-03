import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import P2M.Util
import P2M.Sol.S_LocalNewvector_PSCarrier_existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable
attribute [-instance] FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete FLT.SpectralSide.instCompactSpaceMatrix
attribute [-simp] FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv

theorem LocalNewvector.PSCarrier.existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    (h₁ : LocalNewvector.IsUnramified p μ₁) (h₂ : LocalNewvector.IsUnramified p μ₂)
    (hγ : (μ₁ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ) * ((μ₂ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ))⁻¹ = ((p : ℂ))⁻¹)
    (W : Submodule ℂ (LocalNewvector.PSCarrier p μ₁ μ₂)) (hW : ∀ g : GL (Fin 2) ℚ_[p], ∀ v ∈ W, g • v ∈ W)
    (hb : W ≠ ⊥) :
    ∃! f : LocalNewvector.PSCarrier p μ₁ μ₂,
      f ∈ W ⊓ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p 1) (LocalNewvector.PSCarrier p μ₁ μ₂) ∧
      LocalNewvector.PSCarrier.toFn p μ₁ μ₂ f 1 = 1 ∧
      ∀ k : GL (Fin 2) ℤ_[p],
        ((k : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0 ∈ Ideal.span {(p : ℤ_[p])} →
          LocalNewvector.PSCarrier.toFn p μ₁ μ₂ f (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) k) = 1) ∧
        ((k : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0 ∉ Ideal.span {(p : ℤ_[p])} →
          LocalNewvector.PSCarrier.toFn p μ₁ μ₂ f (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) k)
            = -((p : ℂ))⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_LocalNewvector_PSCarrier_existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable.solution
