import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_abs_le_of_apply_mul_archCircleAt_eq_zpow_mul_of_mem_iSup_archTypeSubmoduleAt
attribute [-instance] AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
p2m_open "AutomorphicForm~isCompact_rowIsometrySubgroup_detOne~exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent"
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_abs_le_of_apply_mul_archCircleAt_eq_zpow_mul_of_mem_iSup_archTypeSubmoduleAt
    (K : Type) [Field K] [NumberField K]
    (tys : ArchTypeFamily K) :
    ∃ n₀ : ℕ,
      ∀ (w : InfinitePlace K) (hw : w.IsComplex) (f : AdelicGL2 (𝓞 K) K → ℂ),
        Continuous f → f ∈ (⨆ i : Fin (tys.card w), archTypeSubmoduleAt K w (tys.rep w i)) →
        ∀ (x₀ : AdelicGL2 (𝓞 K) K) (m : ℤ),
          (∀ ζ : ℂˣ, ‖(ζ : ℂ)‖ = 1 → f (x₀ * archCircleAt hw ζ) = (ζ : ℂ) ^ m * f x₀) →
          f x₀ ≠ 0 → |m| ≤ (n₀ : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_abs_le_of_apply_mul_archCircleAt_eq_zpow_mul_of_mem_iSup_archTypeSubmoduleAt.solution
