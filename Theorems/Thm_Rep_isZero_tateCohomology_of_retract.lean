import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_isZero_tateCohomology_of_retract
attribute [-simp] Rep.coe_tateδneg2_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.isZero_tateCohomology_of_retract {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {A B : Rep.{u} k G} (i : A ⟶ B) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A) (q : ℤ)
    (hB : CategoryTheory.Limits.IsZero (B.tateCohomology q)) :
    CategoryTheory.Limits.IsZero (A.tateCohomology q) := by p2m_exact_reverting @_root_.P2MW.S_Rep_isZero_tateCohomology_of_retract.solution
