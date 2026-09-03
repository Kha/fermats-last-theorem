import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_XOneP_exists_floorHom_isFinite_twoChartIntegralModel_x1_mul_x1x0
attribute [-simp] ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel~finiteType_chartAlgFin_and_chartAlgInf"

theorem ModularCurve.XOneP.exists_floorHom_isFinite_twoChartIntegralModel_x1_mul_x1x0
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))

    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (hle : K₁ ≤ K)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (j₁ : ↥K₁) (hj₁ : ((j₁ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₁ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    ∃ (m : AlgebraicCurve.TwoChartIntegralModel A (↥K) j ⟶ AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j₁)
      (ιF : ↥(chartAlgFin A (↥K₁) j₁) →ₐ[A] ↥(chartAlgFin A (↥K) j))
      (ιI : ↥(chartAlgInf A (↥K₁) j₁) →ₐ[A] ↥(chartAlgInf A (↥K) j)),
      (∀ x, (((ιF x : ↥K) : LaurentSeries L)) = ((x : ↥K₁) : LaurentSeries L)) ∧
      (∀ x, (((ιI x : ↥K) : LaurentSeries L)) = ((x : ↥K₁) : LaurentSeries L)) ∧
      m ≫ toBase A (↥K₁) j₁ = toBase A (↥K) j ∧
      Spec.map (CommRingCat.ofHom ιF.toRingHom) ≫ ιFin A (↥K₁) j₁ = ιFin A (↥K) j ≫ m ∧
      Spec.map (CommRingCat.ofHom ιI.toRingHom) ≫ ιInf A (↥K₁) j₁ = ιInf A (↥K) j ≫ m ∧
      m ⁻¹ᵁ (ιFin A (↥K₁) j₁).opensRange = (ιFin A (↥K) j).opensRange ∧
      m ⁻¹ᵁ (ιInf A (↥K₁) j₁).opensRange = (ιInf A (↥K) j).opensRange ∧
      IsFinite m ∧ Function.Surjective m.base ∧
      ιF.toRingHom.Finite ∧ ιI.toRingHom.Finite ∧
      (∀ x : ↥K, x ∈ chartAlgFin A (↥K) j ↔
        IsIntegral ↥((ιF.range).map (chartAlgFin A (↥K) j).val) x) ∧
      (∀ x : ↥K, x ∈ chartAlgInf A (↥K) j ↔
        IsIntegral ↥((ιI.range).map (chartAlgInf A (↥K) j).val) x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XOneP_exists_floorHom_isFinite_twoChartIntegralModel_x1_mul_x1x0.solution
