import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BorelSubgroup
import P2M.Util
import P2M.Sol.S_NumberField_InfiniteAdeleRing_exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped ENNReal

attribute [local instance] AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

theorem NumberField.InfiniteAdeleRing.exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (lam : Measure (InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    (μB : @Measure ↥(AutomorphicForm.borelSubgroup (InfiniteAdeleRing K)) (borel _))
    (hμB : @Measure.IsHaarMeasure _ _ _ (borel _) μB) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ F : GL (Fin 2) (InfiniteAdeleRing K) → ℝ≥0∞, Measurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] F →
        @lintegral _ (borel _) μB (fun b => F (b : GL (Fin 2) (InfiniteAdeleRing K))) =
          c * ∫⁻ u, ∫⁻ t, ∫⁻ x,
                F (Matrix.GeneralLinearGroup.scalar (Fin 2) u * diagUnits2 t 1 * AutomorphicForm.unipotentGL2 x)
              ∂lam ∂ρ ∂ρ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfiniteAdeleRing_exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2.solution
