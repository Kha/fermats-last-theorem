import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import P2M.Util
import P2M.Sol.S_Rep_IsTateCupProduct_exists_cupEv_dual_right_eq

set_option autoImplicit false
open CategoryTheory Rep MonoidalCategory
theorem Rep.IsTateCupProduct.exists_cupEv_dual_right_eq {G : Type} [Group G] [Fintype G]
    {cup : Rep.TateCupFamily ℤ G} (hcup : Rep.IsTateCupProduct cup)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] [Module.Finite ℤ V] (ρ : Representation ℤ G V)
    (p q : ℤ) (h : p + q = 0) (φ : (Rep.of ρ).tateCohomology p →ₗ[ℤ] (Rep.trivial ℤ G ℤ).tateCohomology 0) :
    ∃ b : ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)).tateCohomology q,
      ∀ x : (Rep.of ρ).tateCohomology p,
        (Rep.tateMap ((ihom.ev (Rep.of ρ)).app (Rep.trivial ℤ G ℤ)) 0).hom
          (cup (Rep.of ρ) ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)) p q 0 h x b) = φ x := by p2m_exact_reverting @_root_.P2MW.S_Rep_IsTateCupProduct_exists_cupEv_dual_right_eq.solution
