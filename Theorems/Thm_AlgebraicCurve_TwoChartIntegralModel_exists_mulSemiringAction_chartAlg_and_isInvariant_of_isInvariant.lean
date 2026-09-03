import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_mulSemiringAction_chartAlg_and_isInvariant_of_isInvariant

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u v

theorem AlgebraicCurve.TwoChartIntegralModel.exists_mulSemiringAction_chartAlg_and_isInvariant_of_isInvariant
    (R : Type u) [CommRing R]
    (K₂ : Type u) [Field K₂] [Algebra R K₂]
    (K₁ : Type u) [Field K₁] [Algebra R K₁] [Algebra K₂ K₁] [IsScalarTower R K₂ K₁]
    (G : Type v) [Group G] [MulSemiringAction G K₁] [SMulCommClass G K₂ K₁]
    [Algebra.IsInvariant K₂ K₁ G]
    (S₂ : Set K₂) (S₁ : Set K₁) (hS : algebraMap K₂ K₁ '' S₂ = S₁)
    (ι : ↥(chartAlg R K₂ S₂) →ₐ[R] ↥(chartAlg R K₁ S₁))
    (hι : ∀ x : ↥(chartAlg R K₂ S₂), ((ι x : ↥(chartAlg R K₁ S₁)) : K₁) = algebraMap K₂ K₁ (x : K₂)) :
    ∃ (_ : MulSemiringAction G ↥(chartAlg R K₁ S₁)),

      (∀ (g : G) (x : ↥(chartAlg R K₁ S₁)), ((g • x : ↥(chartAlg R K₁ S₁)) : K₁) = g • (x : K₁)) ∧

      SMulCommClass G R ↥(chartAlg R K₁ S₁) ∧

      (letI : Algebra ↥(chartAlg R K₂ S₂) ↥(chartAlg R K₁ S₁) := ι.toRingHom.toAlgebra
       SMulCommClass G ↥(chartAlg R K₂ S₂) ↥(chartAlg R K₁ S₁) ∧
         Algebra.IsInvariant ↥(chartAlg R K₂ S₂) ↥(chartAlg R K₁ S₁) G) ∧

      (FaithfulSMul G K₁ → IsFractionRing ↥(chartAlg R K₁ S₁) K₁ → FaithfulSMul G ↥(chartAlg R K₁ S₁)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_mulSemiringAction_chartAlg_and_isInvariant_of_isInvariant.solution
