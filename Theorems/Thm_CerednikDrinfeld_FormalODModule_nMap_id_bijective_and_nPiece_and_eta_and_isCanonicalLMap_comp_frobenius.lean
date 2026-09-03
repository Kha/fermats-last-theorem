import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_ODModuleFrobeniusTwist
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_nMap_id_bijective_and_nPiece_and_eta_and_isCanonicalLMap_comp_frobenius

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.FormalODModule.nMap_id_bijective_and_nPiece_and_eta_and_isCanonicalLMap_comp_frobenius
    (p : ℕ) [Fact p.Prime] {C : Type} [CommRing C] (X : FormalODModule p C) (j : Zp2 p →+* C)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (hc' : IsCompl (X.gradedPiece (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) 0)
      (X.gradedPiece (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) 1))
    (I : (X.toGradedCartierModuleData j hc).NMod →+ (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').NMod)
    (hI : ∀ x y : MvFormalGroup.CartierModule p X.F, I ((X.toGradedCartierModuleData j hc).nMk (x, y)) = (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').nMk (x, y)) :
    Function.Bijective I ∧
    (∀ z, I ((X.toGradedCartierModuleData j hc).nVarpi z) = (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').nVarpi (I z)) ∧
    (∀ (i : Fin 2) (z : (X.toGradedCartierModuleData j hc).NMod), z ∈ (X.toGradedCartierModuleData j hc).nPiece i ↔ I z ∈ (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').nPiece (i + 1)) ∧
    (∀ (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod) (hL : (X.toGradedCartierModuleData j hc).IsCartierLMap L),
      ∃ hL' : (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').IsCartierLMap (I.comp L),
        (∀ (i : Fin 2) (z : (X.toGradedCartierModuleData j hc).NMod), z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.map_verschiebung i ↔
          I z ∈ (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').etaPiece (I.comp L) hL'.map_verschiebung (i + 1)) ∧
        ((X.toGradedCartierModuleData j hc).IsCanonicalLMap L ↔ (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').IsCanonicalLMap (I.comp L))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_nMap_id_bijective_and_nPiece_and_eta_and_isCanonicalLMap_comp_frobenius.solution
