import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import P2M.Util
import P2M.Sol.S_Rep_IsTateCupProduct_cupEv_characterDual_eq_zero

set_option autoImplicit false
open CategoryTheory Rep MonoidalCategory
theorem Rep.IsTateCupProduct.cupEv_characterDual_eq_zero {G : Type} [Group G] [Fintype G]
    {cup : Rep.TateCupFamily ℤ G} (hcup : Rep.IsTateCupProduct cup) (M : Rep ℤ G) (p q : ℤ) (h : p + q = -1)
    (a : ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).tateCohomology q)
    (ha : ∀ x : M.tateCohomology p,
      (Rep.tateMap ((ihom.ev M).app (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1)).hom
        (cup M ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) p q (-1) h x a) = 0) :
    a = 0 := by p2m_exact_reverting @_root_.P2MW.S_Rep_IsTateCupProduct_cupEv_characterDual_eq_zero.solution
