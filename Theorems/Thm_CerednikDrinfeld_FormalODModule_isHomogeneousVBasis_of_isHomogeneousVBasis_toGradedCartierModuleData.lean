import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup open MvFormalGroup.CartierModule hiding tangent_surjective_of_algebra_padicInt

open scoped PadicInt

theorem CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] [Algebra ℤ_[p] S] (j : Zp2 p →+* S)
    (X : FormalODModule p S) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (γ : Fin 2 → CartierModule p X.F)
    (hγ : (X.toGradedCartierModuleData j hc).IsHomogeneousVBasis γ) :
    X.IsHomogeneousVBasis j γ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData.solution
