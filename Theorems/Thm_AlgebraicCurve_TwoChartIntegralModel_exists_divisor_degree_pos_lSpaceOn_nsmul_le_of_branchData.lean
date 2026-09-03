import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_divisor_degree_pos_lSpaceOn_nsmul_le_of_branchData

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.exists_divisor_degree_pos_lSpaceOn_nsmul_le_of_branchData
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F] [IsCurveOver K₀ F]
    (f : F) [Fact (f ≠ 0)] (htf : Transcendental R f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (𝔪 : ι → Ideal ↥(chartAlgFin R F f)) (h𝔪 : ∀ i, (𝔪 i).IsMaximal)
    (hϖ𝔪 : ∀ i, algebraMap R ↥(chartAlgFin R F f) ϖ ∈ 𝔪 i) (hf𝔪 : ∀ i, jChartFin R F f ∈ 𝔪 i)
    (I : ι → Ideal ↥(chartAlgFin R F f))
    (hI : ∀ i (a : ↥(chartAlgFin R F f)), a ∈ I i ↔
      ∃ s : ↥(chartAlgFin R F f), s ∉ 𝔪 i ∧ s * a ∈ Ideal.span {jChartFin R F f})
    (hne : ∀ i, I i ≠ ⊤)
    (htor : ∀ i (y : ↥(chartAlgFin R F f) ⧸ I i), algebraMap R (↥(chartAlgFin R F f) ⧸ I i) ϖ * y = 0 → y = 0)
    (hle : ∀ i (P : Ideal ↥(chartAlgFin R F f)), P.IsPrime → I i ≤ P → P ≤ 𝔪 i) :
    ∃ D_K : Divisor K₀ F, 0 ≤ D_K ∧ 0 < Divisor.degree D_K ∧
      (∀ v : Place K₀ F, f⁻¹ ∈ v.toValuationSubring → D_K v = 0) ∧
      ∀ n : ℕ,

        (∀ g : F, g ∈ lSpaceOn {v : Place K₀ F | f ∈ v.toValuationSubring} ((n : ℤ) • D_K) →
          ∃ k : ℕ, ∀ a ∈ (∏ i, I i) ^ n, ∃ b : ↥(chartAlgFin R F f),
            algebraMap R F ϖ ^ k * g * (a : F) = (b : F)) ∧

        (∀ z : ↥(chartAlgMid R F f), (z : F) ∈
          lSpaceOn ({v : Place K₀ F | f ∈ v.toValuationSubring} ∩ {v : Place K₀ F | f⁻¹ ∈ v.toValuationSubring})
            ((n : ℤ) • D_K)) ∧

        (∀ g : F, g ∈ lSpaceOn {v : Place K₀ F | f⁻¹ ∈ v.toValuationSubring} ((n : ℤ) • D_K) →
          ∃ (k : ℕ) (b : ↥(chartAlgInf R F f)), algebraMap R F ϖ ^ k * g = (b : F)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_divisor_degree_pos_lSpaceOn_nsmul_le_of_branchData.solution
