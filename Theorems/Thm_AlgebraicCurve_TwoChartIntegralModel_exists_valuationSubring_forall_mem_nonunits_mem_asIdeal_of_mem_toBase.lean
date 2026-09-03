import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_forall_mem_nonunits_mem_asIdeal_of_mem_toBase

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_forall_mem_nonunits_mem_asIdeal_of_mem_toBase
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ)
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (hx : ϖ ∈ ((AlgebraicCurve.TwoChartIntegralModel.toBase R F j).base x).asIdeal) :
    ∃ V : ValuationSubring F,
      IsDiscreteValuationRing ↥V ∧
      (∀ f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j), (f : F) ∈ V) ∧
      (∀ f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j), (f : F) ∈ V) ∧
      algebraMap R F ϖ ∈ V.nonunits ∧
      (∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin R F j), (AlgebraicCurve.TwoChartIntegralModel.ιFin R F j).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j), (b : F) ∈ V.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf R F j), (AlgebraicCurve.TwoChartIntegralModel.ιInf R F j).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j), (b : F) ∈ V.nonunits → b ∈ y.asIdeal) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_forall_mem_nonunits_mem_asIdeal_of_mem_toBase.solution
