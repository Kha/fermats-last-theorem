import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_nonempty_tateCohomology_iso_add_two

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.nonempty_tateCohomology_iso_add_two
    {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (q : ℤ) :
    Nonempty (A.tateCohomology q ≅ A.tateCohomology (q + 2)) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_tateCohomology_iso_add_two.solution
