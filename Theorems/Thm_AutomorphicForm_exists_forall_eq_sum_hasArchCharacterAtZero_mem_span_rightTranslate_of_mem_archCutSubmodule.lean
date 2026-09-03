import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_eq_sum_hasArchCharacterAtZero_mem_span_rightTranslate_of_mem_archCutSubmodule
attribute [-instance] AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar
attribute [-simp] AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering open AutomorphicForm.CuspidalConstituent hiding exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_eq_sum_hasArchCharacterAtZero_mem_span_rightTranslate_of_mem_archCutSubmodule
    (K : Type) [Field K] [NumberField K]
    (tys : ArchTypeFamily K) :
    ∃ n₀ : ℕ,
      ∀ b : AdelicGL2 (𝓞 K) K → ℂ, Continuous b → b ∈ archCutSubmodule K tys →
        ∀ (w : InfinitePlace K) (hw : w.IsReal),
          ∃ c : ℤ → AdelicGL2 (𝓞 K) K → ℂ,
            (∀ n : ℤ, HasArchCharacterAt₀ K w (archWeightCharAt hw n) (c n)) ∧
            (∀ n : ℤ, c n ∈ Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
              rightTranslate K (rowIsometryInclAt₀ K w k) b)) ∧
            (∀ n : ℤ, (n₀ : ℤ) < |n| → c n = 0) ∧
            b = ∑ n ∈ Finset.Icc (-(n₀ : ℤ)) n₀, c n := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_eq_sum_hasArchCharacterAtZero_mem_span_rightTranslate_of_mem_archCutSubmodule.solution
