import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isDomain_tensorProduct_chartAlg_of_finrank_le_finrank_adjoin_range

set_option autoImplicit false

open scoped TensorProduct
open AlgebraicCurve

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.isDomain_tensorProduct_chartAlg_of_finrank_le_finrank_adjoin_range
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
    (k : Type u) [Field k] [Algebra R k] (hk : algebraMap R k ϖ = 0)
    (Ω : Type u) [Field Ω] [Algebra k Ω]
    (ρ : ↥V →+* Ω) (hρ : ∀ x : ↥V, (x : F) ∈ V.nonunits → ρ x = 0)
    (hρR : ∀ r : R, ρ ⟨algebraMap R F r, hRV r⟩ = algebraMap k Ω (algebraMap R k r))
    (jV : ↥V) (hjV' : (jV : F) = j)
    (t : ↥(IntermediateField.adjoin k (Set.range ρ))) (ht : (t : Ω) = ρ jV)
    (htr : Transcendental k t)
    (hdeg : Module.finrank ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F ≤
      Module.finrank ↥(IntermediateField.adjoin k ({t} : Set ↥(IntermediateField.adjoin k (Set.range ρ))))
        ↥(IntermediateField.adjoin k (Set.range ρ))) :
    IsDomain (k ⊗[R] ↥(chartAlgFin R F j)) ∧ IsDomain (k ⊗[R] ↥(chartAlgInf R F j)) ∧
      Nontrivial (k ⊗[R] ↥(chartAlgMid R F j)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isDomain_tensorProduct_chartAlg_of_finrank_le_finrank_adjoin_range.solution
