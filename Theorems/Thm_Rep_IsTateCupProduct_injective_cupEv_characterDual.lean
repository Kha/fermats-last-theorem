import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import P2M.Util
import P2M.Sol.S_Rep_IsTateCupProduct_injective_cupEv_characterDual

set_option autoImplicit false
open CategoryTheory Rep MonoidalCategory
theorem Rep.IsTateCupProduct.injective_cupEv_characterDual {G : Type} [Group G] [Fintype G]
    {cup : Rep.TateCupFamily ℤ G} (hcup : Rep.IsTateCupProduct cup) (M : Rep ℤ G) (p q : ℤ) (h : p + q = -1) :
    Function.Injective (fun x : M.tateCohomology p =>
      ((Rep.tateMap ((ihom.ev M).app (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1)).hom ∘ₗ
        cup M ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) p q (-1) h x :
          ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).tateCohomology q →ₗ[ℤ]
            (Rep.trivial ℤ G (AddCircle (1 : ℚ))).tateCohomology (-1))) := by p2m_exact_reverting @_root_.P2MW.S_Rep_IsTateCupProduct_injective_cupEv_characterDual.solution
