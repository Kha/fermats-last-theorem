import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import P2M.Util
import P2M.Sol.S_Rep_nonempty_twist_inv_twist_iso

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation
open scoped Classical

theorem Rep.nonempty_twist_inv_twist_iso {k : Type} [CommRing k] {G : Type} [Group G] (N : Rep.{0} k G) (χ : G →* kˣ) :
    Nonempty ((N.twist χ⁻¹).twist χ ≅ N) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_twist_inv_twist_iso.solution
