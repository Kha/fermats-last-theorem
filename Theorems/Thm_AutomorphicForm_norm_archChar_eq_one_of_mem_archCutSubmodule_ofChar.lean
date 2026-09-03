import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_norm_archChar_eq_one_of_mem_archCutSubmodule_ofChar
attribute [-instance] AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar
attribute [-simp] AutomorphicForm.CuspidalConstituent.rightRegular_apply

set_option autoImplicit false

open NumberField IsDedekindDomain
open AutomorphicForm

theorem AutomorphicForm.norm_archChar_eq_one_of_mem_archCutSubmodule_ofChar
    (F : Type) [Field F] [NumberField F]
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) (hne : φ ≠ 0)
    (hχ : φ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ)) :
    ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ‖((χ w k : ℂˣ) : ℂ)‖ = 1 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_norm_archChar_eq_one_of_mem_archCutSubmodule_ofChar.solution
