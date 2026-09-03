import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_span_singleton_isPrime_and_mem_iff_mem_nonunits_of_valuationSubring
set_option autoImplicit false

open scoped TensorProduct
open AlgebraicCurve

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.span_singleton_isPrime_and_mem_iff_mem_nonunits_of_valuationSubring
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ)
    (V : ValuationSubring F)
    (hRV : ∀ r : R, algebraMap R F r ∈ V) (hϖV : algebraMap R F ϖ ∈ V.nonunits)
    (hjV : ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)

    (hunif : ∀ f : F, f ∈ V.nonunits → f * (algebraMap R F ϖ)⁻¹ ∈ V)

    (huniq : ∀ V' : ValuationSubring F, (∀ r : R, algebraMap R F r ∈ V') → algebraMap R F ϖ ∈ V'.nonunits →
      (∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval j P ∈ V' ∧ (Polynomial.aeval j P)⁻¹ ∈ V') → V' = V) :
    (∀ a : ↥(TwoChartIntegralModel.chartAlgFin R F j), (a : F) ∈ V) ∧
    (Ideal.span {algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ}).IsPrime ∧
    (∀ a : ↥(TwoChartIntegralModel.chartAlgFin R F j),
      a ∈ Ideal.span {algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ} ↔ (a : F) ∈ V.nonunits) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_span_singleton_isPrime_and_mem_iff_mem_nonunits_of_valuationSubring.solution
