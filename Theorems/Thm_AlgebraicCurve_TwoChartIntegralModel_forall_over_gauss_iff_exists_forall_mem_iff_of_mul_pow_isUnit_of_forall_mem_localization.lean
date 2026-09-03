import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization

set_option autoImplicit false

universe u

p2m_open "IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel~exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin~jInvChartInf_not_mem_of_mem_minimalPrimes_span~mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin"

theorem AlgebraicCurve.TwoChartIntegralModel.forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (f : F) [Fact (f ≠ 0)] (htf : Transcendental R f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    {ι : Type u} [Fintype ι]

    (𝔮 : ι → Ideal ↥(chartAlgFin R F f))
    (h𝔮 : ∀ i, 𝔮 i ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}).minimalPrimes)
    (𝔪 : ι → Ideal ↥(chartAlgFin R F f)) (h𝔪 : ∀ i, (𝔪 i).IsMaximal) (h𝔮𝔪 : ∀ i, 𝔮 i ≤ 𝔪 i)
    (honly : ∀ i, ∀ 𝔮' ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}).minimalPrimes, 𝔮' ≤ 𝔪 i → 𝔮' = 𝔮 i)

    (t : ι → ↥(chartAlgFin R F f)) (ht : ∀ i, t i ∈ 𝔪 i) (ht𝔮 : ∀ i, t i ∉ 𝔮 i)
    (I : ι → Ideal ↥(chartAlgFin R F f)) (htI : ∀ i, t i ∈ I i)
    (hle : ∀ i (P : Ideal ↥(chartAlgFin R F f)), P.IsPrime → I i ≤ P → P ≤ 𝔪 i)

    (n : ℕ) (hn : 1 ≤ n) (g : F)
    (h1 : ∀ 𝔭 : Ideal ↥(chartAlgFin R F f), 𝔭.IsPrime → (∀ i, ¬ I i ≤ 𝔭) →
      ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔭 ∧ g * (c : F) = (b : F))
    (h2 : ∀ 𝔭' : Ideal ↥(chartAlgInf R F f), 𝔭'.IsPrime → jInvChartInf R F f ∈ 𝔭' →
      ∃ b c : ↥(chartAlgInf R F f), c ∉ 𝔭' ∧ g * (c : F) = (b : F))
    (h3 : ∀ i, ∃ b c : ↥(chartAlgFin R F f), b ∉ 𝔪 i ∧ c ∉ 𝔪 i ∧ g * (t i : F) ^ n * (c : F) = (b : F)) :
    (Nonempty ι → Transcendental R g) ∧
    ∀ O : ValuationSubring F, (∀ a : R, algebraMap R F a ∈ O) → algebraMap R F ϖ ∈ O.nonunits →
      ((∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval g P ∈ O ∧ (Polynomial.aeval g P)⁻¹ ∈ O) ↔
        ∃ i, ∀ y : F, y ∈ O ↔ ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔮 i ∧ y * (c : F) = (b : F)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization.solution
