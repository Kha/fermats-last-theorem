import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_KummerCharacter
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_selmerStable_eq_selmer

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith

theorem NumberField.LevelArith.selmerStable_eq_selmer
    (E F : Type) [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) (p : ℕ) :
    selmerStable E F S p = selmer E F S p := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_selmerStable_eq_selmer.solution
