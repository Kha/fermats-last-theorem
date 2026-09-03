import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_nonempty_tateHneg1_linearEquiv_homology_subCompNormHom

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.nonempty_tateHneg1_linearEquiv_homology_subCompNormHom
    {k G : Type u} [CommRing k] [CommGroup G] [Fintype G] (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nonempty (A.tateHneg1 ≃ₗ[k] (FiniteCyclicGroup.subCompNormHom A g).homology) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_tateHneg1_linearEquiv_homology_subCompNormHom.solution
