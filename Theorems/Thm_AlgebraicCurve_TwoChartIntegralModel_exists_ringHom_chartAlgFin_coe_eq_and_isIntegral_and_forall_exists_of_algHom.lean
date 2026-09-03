import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_ringHom_chartAlgFin_coe_eq_and_isIntegral_and_forall_exists_of_algHom

set_option autoImplicit false

universe u

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.exists_ringHom_chartAlgFin_coe_eq_and_isIntegral_and_forall_exists_of_algHom
    (R : Type u) [CommRing R]
    (F'' : Type u) [Field F''] [Algebra R F''] (F : Type u) [Field F] [Algebra R F]
    (φ : F'' →ₐ[R] F)
    (j'' : F'') [Fact (j'' ≠ 0)] (j : F) [Fact (j ≠ 0)] (hφj : φ j'' = j) :
    ∃ ι : ↥(chartAlgFin R F'' j'') →+* ↥(chartAlgFin R F j),
      (∀ x : ↥(chartAlgFin R F'' j''), ((ι x : ↥(chartAlgFin R F j)) : F) = φ (x : F'')) ∧
      ι.IsIntegral ∧
      (∀ y : ↥(chartAlgFin R F j), (y : F) ∈ Set.range φ → ∃ x : ↥(chartAlgFin R F'' j''), ι x = y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_ringHom_chartAlgFin_coe_eq_and_isIntegral_and_forall_exists_of_algHom.solution
