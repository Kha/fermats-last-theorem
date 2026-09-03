import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_of_algEquiv_apply_eq_xH_of_eq_three

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_of_algEquiv_apply_eq_xH_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A)
    (σ : ↥K ≃ₐ[L] ↥K) (hσj : σ j = j)
    (Y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) [Y.IsPrime]
    (hY : ∀ (Cm : Type) [CommRing Cm] [Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) Cm]
      [IsLocalization.AtPrime Cm Y],
      IsRegularLocalRing Cm ∧
        IsRegularLocalRing (Cm ⧸ Ideal.span {algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) Cm
          (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ)}))
    (Y' : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) [Y'.IsPrime]
    (hY' : ∀ b' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), b' ∈ Y' ↔
      ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), b ∈ Y ∧ ((b' : ↥K)) = σ (b : ↥K))
    (Bm : Type) [CommRing Bm] [Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) Bm] [IsLocalization.AtPrime Bm Y'] :
    IsRegularLocalRing Bm ∧
      IsRegularLocalRing (Bm ⧸ Ideal.span {algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) Bm
        (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ)}) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_of_algEquiv_apply_eq_xH_of_eq_three.solution
