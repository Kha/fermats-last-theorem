import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_nonempty_repTorsionP_iso_repModP

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith Pointwise

theorem NumberField.LevelArith.nonempty_repTorsionP_iso_repModP
    {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (hG : (Nat.card G).Coprime p)
    (A : Rep.{0} ℤ G) [Finite A] :
    Nonempty (repTorsionP p A ≅ repModP p A) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_nonempty_repTorsionP_iso_repModP.solution
