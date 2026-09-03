import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_place_forall_mem_and_forall_mem_nonunits_of_forall_mul_eq_zero_imp

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.exists_place_forall_mem_and_forall_mem_nonunits_of_forall_mul_eq_zero_imp
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (f : F) [Fact (f ≠ 0)] (htf : Transcendental R f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (I : Ideal ↥(chartAlgFin R F f)) (hne : I ≠ ⊤) (hfI : jChartFin R F f ∈ I)
    (htor : ∀ y : ↥(chartAlgFin R F f) ⧸ I, algebraMap R (↥(chartAlgFin R F f) ⧸ I) ϖ * y = 0 → y = 0) :
    ∃ v : Place K₀ F, (∀ a : ↥(chartAlgFin R F f), (a : F) ∈ v.toValuationSubring) ∧
      ∀ a ∈ I, (a : F) ∈ v.toValuationSubring.nonunits := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_place_forall_mem_and_forall_mem_nonunits_of_forall_mul_eq_zero_imp.solution
