import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import P2M.Util
import P2M.Sol.S_Rep_IsTateCupProduct_cup_comm

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.IsTateCupProduct.cup_comm {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B : Rep.{u} k G)
    (p q r : ℤ) (h : p + q = r) (x : A.tateCohomology p) (y : B.tateCohomology q) :
    cup B A q p r (by omega) y x
      = (((p * q).negOnePow : ℤ) : k) • (Rep.tateMap (β_ A B).hom r).hom (cup A B p q r h x y) := by p2m_exact_reverting @_root_.P2MW.S_Rep_IsTateCupProduct_cup_comm.solution
