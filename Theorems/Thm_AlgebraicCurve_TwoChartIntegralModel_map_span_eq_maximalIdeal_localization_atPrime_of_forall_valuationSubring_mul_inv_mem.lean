import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_map_span_eq_maximalIdeal_localization_atPrime_of_forall_valuationSubring_mul_inv_mem

set_option autoImplicit false

universe u

open AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.map_span_eq_maximalIdeal_localization_atPrime_of_forall_valuationSubring_mul_inv_mem
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ)
    (hmult : ∀ V : ValuationSubring F, (∀ r : R, algebraMap R F r ∈ V) → algebraMap R F ϖ ∈ V.nonunits →
      (∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
      ∀ x : F, x ∈ V.nonunits → x * (algebraMap R F ϖ)⁻¹ ∈ V)
    (𝔭 : Ideal ↥(chartAlgFin R F j)) [𝔭.IsPrime]
    (h𝔭 : 𝔭 ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes) :
    Ideal.map (algebraMap ↥(chartAlgFin R F j) (Localization.AtPrime 𝔭))
        (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}) =
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_map_span_eq_maximalIdeal_localization_atPrime_of_forall_valuationSubring_mul_inv_mem.solution
