import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_forall_aeval_mem_and_inv_mem_of_mul_pow_mul_eq_of_le_of_isMaximal

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.forall_aeval_mem_and_inv_mem_of_mul_pow_mul_eq_of_le_of_isMaximal
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (f : F) [Fact (f ≠ 0)]
    (𝔮 : Ideal ↥(chartAlgFin R F f)) [𝔮.IsPrime] (hϖ𝔮 : algebraMap R ↥(chartAlgFin R F f) ϖ ∈ 𝔮)
    (𝔪 : Ideal ↥(chartAlgFin R F f)) (h𝔪 : 𝔪.IsMaximal) (h𝔮𝔪 : 𝔮 ≤ 𝔪)
    (t : ↥(chartAlgFin R F f)) (ht : t ∈ 𝔪) (ht𝔮 : t ∉ 𝔮)
    (n : ℕ) (hn : 1 ≤ n) (g : F)
    (hg : ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔮 ∧ g * (c : F) = (b : F))
    (h3 : ∃ b c : ↥(chartAlgFin R F f), b ∉ 𝔪 ∧ c ∉ 𝔪 ∧ g * (t : F) ^ n * (c : F) = (b : F))
    (O : ValuationSubring F)
    (hO : ∀ y : F, y ∈ O ↔ ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔮 ∧ y * (c : F) = (b : F)) :
    ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval g P ∈ O ∧ (Polynomial.aeval g P)⁻¹ ∈ O := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_aeval_mem_and_inv_mem_of_mul_pow_mul_eq_of_le_of_isMaximal.solution
