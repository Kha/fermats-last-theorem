import Definitions.Def_NumberField_IdeleProductMeasure
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import P2M.Util
import P2M.Sol.S_NumberField_Idele_exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity
attribute [-simp] NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply

set_option autoImplicit false

open scoped Classical

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem NumberField.Idele.exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity
    (K : Type) [Field K] [NumberField K] :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      Measure.map (fun a : (AdeleRing (𝓞 K) K)ˣ =>
          InfiniteAdeleRing.ringEquiv_mixedSpace K ((a : AdeleRing (𝓞 K) K)).1)
        (NumberField.Idele.sPartMeasure K ∅) =
      C • (volume : Measure (mixedEmbedding.mixedSpace K)).withDensity
        (fun z => (ENNReal.ofReal ((∏ w, |z.1 w|) * ∏ w, ‖z.2 w‖ ^ 2))⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity.solution
