import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_natCard_tateCohomology_zero_and_neg_one_of_isCyclic

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.natCard_tateCohomology_zero_and_neg_one_of_isCyclic {k G : Type u} [CommRing k] [Group G] [Fintype G]
    [IsCyclic G] (A : Rep.{u} k G) :
    Nat.card (A.tateCohomology 0) = Nat.card (groupCohomology A 2) ∧
      Nat.card (A.tateCohomology (-1)) = Nat.card (groupCohomology A 1) := by p2m_exact_reverting @_root_.P2MW.S_Rep_natCard_tateCohomology_zero_and_neg_one_of_isCyclic.solution
