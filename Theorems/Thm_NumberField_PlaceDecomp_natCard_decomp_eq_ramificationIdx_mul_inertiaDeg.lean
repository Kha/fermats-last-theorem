import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_natCard_decomp_eq_ramificationIdx_mul_inertiaDeg

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg
    (K K'' : Type) [Field K] [NumberField K] [Field K''] [NumberField K''] [Algebra K K''] [IsGalois K K'']
    (w'' : HeightOneSpectrum (𝓞 K'')) :
    Nat.card (decomp K K'' w'') =
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w'').asIdeal w''.asIdeal *
        Ideal.inertiaDeg' (HeightOneSpectrum.under (𝓞 K) w'').asIdeal w''.asIdeal := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_natCard_decomp_eq_ramificationIdx_mul_inertiaDeg.solution
