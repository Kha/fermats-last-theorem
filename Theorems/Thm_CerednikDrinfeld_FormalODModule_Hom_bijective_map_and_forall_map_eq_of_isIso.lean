import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_Hom_bijective_map_and_forall_map_eq_of_isIso

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.Hom.bijective_map_and_forall_map_eq_of_isIso
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (Y X : CerednikDrinfeld.FormalODModule p B) (u : Y.Hom X) (hu : u.IsIso)
    (g : MvFormalGroup.CartierModule p Y.F →+ MvFormalGroup.CartierModule p X.F)
    (hg : g = MvFormalGroup.CartierModule.map u.toLawHom) :
    Function.Bijective g ∧
    (∀ (w : WittVector p B) (m : MvFormalGroup.CartierModule p Y.F),
      g (w • m) = w • g m) ∧
    (∀ m : MvFormalGroup.CartierModule p Y.F,
      g (MvFormalGroup.CartierModule.frobenius m) =
        MvFormalGroup.CartierModule.frobenius (g m)) ∧
    (∀ m : MvFormalGroup.CartierModule p Y.F,
      g (MvFormalGroup.CartierModule.verschiebungInt m) =
        MvFormalGroup.CartierModule.verschiebungInt (g m)) ∧
    (∀ m : MvFormalGroup.CartierModule p Y.F,
      g (MvFormalGroup.CartierModule.endAct Y.varpiEnd m) =
        MvFormalGroup.CartierModule.endAct X.varpiEnd (g m)) ∧
    (∀ (i : ℕ) (m : MvFormalGroup.CartierModule p Y.F),
      m ∈ Y.gradedPiece j i → g m ∈ X.gradedPiece j i) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_Hom_bijective_map_and_forall_map_eq_of_isIso.solution
