import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
    (K K'' : Type) [Field K] [NumberField K] [Field K''] [NumberField K''] [Algebra K K''] [IsGalois K K'']
    (w'' : HeightOneSpectrum (𝓞 K'')) (y : w''.adicCompletion K'') :
    (∀ σ : decomp K K'' w'', σ • y = y) ↔
      y ∈ Set.range (HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
        (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w'').Extension (𝓞 K''))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom.solution
