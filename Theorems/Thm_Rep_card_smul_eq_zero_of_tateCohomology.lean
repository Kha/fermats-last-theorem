import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_card_smul_eq_zero_of_tateCohomology
attribute [-simp] Rep.coe_tateδneg2_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.card_smul_eq_zero_of_tateCohomology {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (q : ℤ) (x : A.tateCohomology q) : (Fintype.card G : k) • x = 0 := by p2m_exact_reverting @_root_.P2MW.S_Rep_card_smul_eq_zero_of_tateCohomology.solution
