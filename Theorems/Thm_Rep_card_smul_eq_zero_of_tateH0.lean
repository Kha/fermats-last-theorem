import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_card_smul_eq_zero_of_tateH0

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.card_smul_eq_zero_of_tateH0 {k G : Type*} [CommRing k] [Group G] [Fintype G] (A : Rep k G)
    (x : A.tateH0) : (Fintype.card G : k) • x = 0 := by p2m_exact_reverting @_root_.P2MW.S_Rep_card_smul_eq_zero_of_tateH0.solution
