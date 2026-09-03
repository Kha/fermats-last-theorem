import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_nonempty_tateCohomology_iso_of_iso

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.nonempty_tateCohomology_iso_of_iso {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {A B : Rep.{u} k G} (e : A ≅ B) (q : ℤ) : Nonempty (A.tateCohomology q ≅ B.tateCohomology q) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_tateCohomology_iso_of_iso.solution
