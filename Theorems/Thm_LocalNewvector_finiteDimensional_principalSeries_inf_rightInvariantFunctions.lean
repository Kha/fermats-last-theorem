import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import P2M.Util
import P2M.Sol.S_LocalNewvector_finiteDimensional_principalSeries_inf_rightInvariantFunctions
attribute [-instance] FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete FLT.SpectralSide.instCompactSpaceMatrix
attribute [-simp] FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalNewvector.unitValuation_apply LocalNewvector.valChar_apply

theorem LocalNewvector.finiteDimensional_principalSeries_inf_rightInvariantFunctions (p : ℕ) [Fact p.Prime]
    (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) (U : Subgroup (GL (Fin 2) ℚ_[p])) (hU : IsOpen (U : Set (GL (Fin 2) ℚ_[p]))) :
    FiniteDimensional ℂ
      ↥(LocalNewvector.principalSeries p μ₁ μ₂ ⊓ LocalNewvector.rightInvariantFunctions p U) := by p2m_exact_reverting @_root_.P2MW.S_LocalNewvector_finiteDimensional_principalSeries_inf_rightInvariantFunctions.solution
