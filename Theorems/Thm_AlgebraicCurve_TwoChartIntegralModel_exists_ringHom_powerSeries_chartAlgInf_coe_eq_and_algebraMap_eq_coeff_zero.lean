import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_ringHom_powerSeries_chartAlgInf_coe_eq_and_algebraMap_eq_coeff_zero
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open AlgebraicCurve

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.exists_ringHom_powerSeries_chartAlgInf_coe_eq_and_algebraMap_eq_coeff_zero
    (L : Type u) [Field L]
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra A L] [IsFractionRing A L]
    (K : IntermediateField L (LaurentSeries L)) [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    (hj : ∀ n : ℤ, n ≤ 0 → ((j : LaurentSeries L)⁻¹).coeff n = 0) :
    ∃ (ι : ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j) →+* PowerSeries L)
      (χ : ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j) →+* A),
      (∀ b : ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j),
        ((ι b : PowerSeries L) : LaurentSeries L) = ((b : ↥K) : LaurentSeries L)) ∧
      (∀ b : ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j),
        algebraMap A L (χ b) = PowerSeries.constantCoeff (ι b)) ∧
      (∀ a : A, ι (algebraMap A ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j) a) =
        PowerSeries.C (algebraMap A L a)) ∧
      ι (TwoChartIntegralModel.jInvChartInf A (↥K) j) =
        PowerSeries.X * PowerSeries.mk (fun n : ℕ => ((j : LaurentSeries L)⁻¹).coeff ((n : ℤ) + 1)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_ringHom_powerSeries_chartAlgInf_coe_eq_and_algebraMap_eq_coeff_zero.solution
