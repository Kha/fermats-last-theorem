import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_isZero_tateCohomology_of_subsingleton

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.isZero_tateCohomology_of_subsingleton {k G : Type u} [CommRing k] [Group G] [Fintype G] [Subsingleton G]
    (A : Rep.{u} k G) (q : ℤ) : CategoryTheory.Limits.IsZero (A.tateCohomology q) := by p2m_exact_reverting @_root_.P2MW.S_Rep_isZero_tateCohomology_of_subsingleton.solution
