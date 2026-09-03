import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_tensor_chartAlgFin_chartRing_and_chartAlgInf_laurentBaseChange_twoChartModel_of_coe_eq_coeffEmb
attribute [-instance] AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve AlgebraicCurve~TwoChartIntegralModel"
open scoped TensorProduct

theorem ModularCurve.exists_algEquiv_tensor_chartAlgFin_chartRing_and_chartAlgInf_laurentBaseChange_twoChartModel_of_coe_eq_coeffEmb
    (p : ℕ) (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j₀ : ↥F₀)
    (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥(ModularCurve.laurentBaseChange L F₀)] [IsScalarTower A L ↥(ModularCurve.laurentBaseChange L F₀)]
    (j : ↥(ModularCurve.laurentBaseChange L F₀)) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ((j₀ : ↥F₀) : LaurentSeries ℚ)) [Fact (j ≠ 0)]
    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]
    (jb : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hjb : (jb : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((j₀ : ↥F₀) : LaurentSeries ℚ)) [Fact (jb ≠ 0)]
    (hmem : ∀ b : ↥(ModularCurve.laurentBaseChange L F₀), ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L) ∈ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀) :
    (∃ eFin : (AlgebraicClosure ℚ) ⊗[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L F₀)) j)
        ≃ₐ[AlgebraicClosure ℚ] ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀))),
      ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L F₀)) j),
        ((eFin ((1 : AlgebraicClosure ℚ) ⊗ₜ[A] b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀)))) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
          ⟨ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L), hmem b⟩) ∧
    (∃ eInf : (AlgebraicClosure ℚ) ⊗[A] ↥(ModularCurve.TwoChart.chartAlgInf A (↥(ModularCurve.laurentBaseChange L F₀)) j)
        ≃ₐ[AlgebraicClosure ℚ] ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀))),
      ∀ b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥(ModularCurve.laurentBaseChange L F₀)) j),
        ((eInf ((1 : AlgebraicClosure ℚ) ⊗ₜ[A] b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀)))) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
          ⟨ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L), hmem b⟩) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_tensor_chartAlgFin_chartRing_and_chartAlgInf_laurentBaseChange_twoChartModel_of_coe_eq_coeffEmb.solution
