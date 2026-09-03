import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental

set_option autoImplicit false

universe u

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (V : ValuationSubring F)
    (hVA : ∀ a : R, algebraMap R F a ∈ V)
    (hVm : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V.nonunits)
    (hVj : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) :

    (∀ b : ↥(chartAlgFin R F j), (b : F) ∈ V) ∧

    (∃ 𝔓 : Ideal ↥(chartAlgFin R F j), 𝔓.IsPrime ∧ 𝔓.height = 1 ∧
      (∀ b : ↥(chartAlgFin R F j), b ∈ 𝔓 ↔ (b : F) ∈ V.nonunits) ∧
      (∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R ↥(chartAlgFin R F j) a ∈ 𝔓) ∧

      (∀ f : F, f ∈ V ↔ ∃ a b : ↥(chartAlgFin R F j), b ∉ 𝔓 ∧ f * (b : F) = (a : F))) ∧

    (∀ V' : ValuationSubring F,
      (∀ a : R, algebraMap R F a ∈ V') →
      (∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V'.nonunits) →
      (∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
        Polynomial.aeval j P ∈ V' ∧ (Polynomial.aeval j P)⁻¹ ∈ V') →
      V ≠ V' →
      ∃ b : ↥(chartAlgFin R F j), (b : F) ∈ V'.nonunits ∧ (b : F) ∉ V.nonunits) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental.solution
