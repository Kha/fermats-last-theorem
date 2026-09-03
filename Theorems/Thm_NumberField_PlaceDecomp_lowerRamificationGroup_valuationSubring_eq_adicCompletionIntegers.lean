import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (w : HeightOneSpectrum (𝓞 F)) (i : ℕ) :
    ValuationSubring.lowerRamificationGroup E ((w.valuation F).valuationSubring) i =
      IsLocalRing.lowerRamificationGroup ↥(w.adicCompletionIntegers F) ↥(NumberField.PlaceDecomp.decomp E F w) i := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers.solution
