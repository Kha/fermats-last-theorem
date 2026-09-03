import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_subsingleton_tateHneg1_ind_bot

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.subsingleton_tateHneg1_ind_bot {k G : Type*} [CommRing k] [Group G] [Fintype G]
    (A : Rep k (⊥ : Subgroup G)) : Subsingleton (Rep.ind (⊥ : Subgroup G).subtype A).tateHneg1 := by p2m_exact_reverting @_root_.P2MW.S_Rep_subsingleton_tateHneg1_ind_bot.solution
