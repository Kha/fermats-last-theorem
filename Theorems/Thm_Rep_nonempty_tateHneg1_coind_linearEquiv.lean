import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_nonempty_tateHneg1_coind_linearEquiv

set_option autoImplicit false
open CategoryTheory Rep
theorem Rep.nonempty_tateHneg1_coind_linearEquiv {k G : Type*} [CommRing k] [Group G] [Fintype G]
    (S : Subgroup G) [Fintype S] (B : Rep k S) :
    Nonempty ((Rep.coind S.subtype B).tateHneg1 ≃ₗ[k] B.tateHneg1) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_tateHneg1_coind_linearEquiv.solution
