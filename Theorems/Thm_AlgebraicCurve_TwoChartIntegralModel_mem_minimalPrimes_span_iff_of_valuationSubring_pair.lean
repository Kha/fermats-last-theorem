import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair

set_option autoImplicit false

universe u

p2m_open "AlgebraicCurve.TwoChartIntegralModel~exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin~le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental"

theorem AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_span_iff_of_valuationSubring_pair
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (W₀ W₁ : ValuationSubring F)

    (h1 : ∀ i : Fin 2, (∀ a : R, algebraMap R F a ∈ (![W₀, W₁] i)) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ (![W₀, W₁] i).nonunits)

    (h2 : ∀ i : Fin 2, ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j P ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval j P)⁻¹ ∈ (![W₀, W₁] i))

    (h3 : W₀ ≠ W₁)

    (h5 : ∀ V : ValuationSubring F,
      (∀ a : R, algebraMap R F a ∈ V) → (∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V.nonunits) →
      (∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₁) :

    (∀ 𝔭 ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes,
      (∀ b : ↥(chartAlgFin R F j), b ∈ 𝔭 ↔ (b : F) ∈ W₀.nonunits) ∨
      (∀ b : ↥(chartAlgFin R F j), b ∈ 𝔭 ↔ (b : F) ∈ W₁.nonunits)) ∧

    (∀ i : Fin 2, ∃ 𝔭 ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes,
      ∀ b : ↥(chartAlgFin R F j), b ∈ 𝔭 ↔ (b : F) ∈ (![W₀, W₁] i).nonunits) ∧

    (∃ b : ↥(chartAlgFin R F j), (b : F) ∈ W₀.nonunits ∧ (b : F) ∉ W₁.nonunits) ∧
    (∃ b : ↥(chartAlgFin R F j), (b : F) ∈ W₁.nonunits ∧ (b : F) ∉ W₀.nonunits) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair.solution
