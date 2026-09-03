import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_natCard_tateCohomology_zero_trivial_int

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.natCard_tateCohomology_zero_trivial_int {G : Type} [Group G] [Fintype G] :
    Nat.card ((Rep.trivial ℤ G ℤ).tateCohomology 0) = Fintype.card G := by p2m_exact_reverting @_root_.P2MW.S_Rep_natCard_tateCohomology_zero_trivial_int.solution
