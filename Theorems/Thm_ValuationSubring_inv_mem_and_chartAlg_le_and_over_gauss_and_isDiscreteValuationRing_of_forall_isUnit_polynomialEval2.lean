import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_ValuationSubring_inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem ValuationSubring.inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (O : ValuationSubring F)
    (hRO : ∀ a : R, algebraMap R F a ∈ O) (hϖO : algebraMap R F ϖ ∈ O.nonunits)
    (f : F) (hfO : f ∈ O)
    (hgeo : ∀ p : Polynomial R, (∃ i, IsUnit (p.coeff i)) →
      ∃ hO : Polynomial.eval₂ (algebraMap R F) f p ∈ O, IsUnit (⟨_, hO⟩ : ↥O)) :
    ∃ hf0 : f ≠ 0,
      letI : Fact (f ≠ 0) := ⟨hf0⟩
      f⁻¹ ∈ O ∧ Transcendental R f ∧

      (∀ x : ↥(chartAlgFin R F f), (x : F) ∈ O) ∧ (∀ x : ↥(chartAlgInf R F f), (x : F) ∈ O) ∧

      (∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval f P ∈ O ∧ (Polynomial.aeval f P)⁻¹ ∈ O) ∧

      (FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F →
        Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F →
        IsDiscreteValuationRing ↥O ∧
        ∃ 𝔭 : Ideal ↥(chartAlgFin R F f),
          𝔭 ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}).minimalPrimes ∧ ¬ 𝔭.IsMaximal ∧
          (∀ x : ↥(chartAlgFin R F f), x ∈ 𝔭 ↔ (x : F) ∈ O.nonunits) ∧
          (∀ y : F, y ∈ O ↔ ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔭 ∧ y * (c : F) = (b : F))) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2.solution
