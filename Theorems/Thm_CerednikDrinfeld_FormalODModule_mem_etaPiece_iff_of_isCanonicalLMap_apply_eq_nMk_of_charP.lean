import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (X : FormalODModule p B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (htors : ∀ m : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.endAct X.varpiEnd m = 0 → m = 0)
    (i : Fin 2) (hi : ∀ m ∈ X.gradedPiece j (i : ℕ),
      ∃ g : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.verschiebungInt g = MvFormalGroup.CartierModule.endAct X.varpiEnd m)
    (hLi : ∀ x y : MvFormalGroup.CartierModule p X.F, x ∈ X.gradedPiece j (i : ℕ) →
      MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct X.varpiEnd x → L x = (X.toGradedCartierModuleData j hc).nMk (y, 0)) :
    (∀ z : (X.toGradedCartierModuleData j hc).NMod,
      z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i ↔
        ∃ m : MvFormalGroup.CartierModule p X.F, m ∈ X.gradedPiece j (i : ℕ) ∧
          MvFormalGroup.CartierModule.endAct X.varpiEnd m = MvFormalGroup.CartierModule.verschiebungInt m ∧ z = (X.toGradedCartierModuleData j hc).nMk (m, 0)) ∧
    (∀ m m' : MvFormalGroup.CartierModule p X.F, m ∈ X.gradedPiece j (i : ℕ) → m' ∈ X.gradedPiece j (i : ℕ) →
      (X.toGradedCartierModuleData j hc).nMk (m, 0) = (X.toGradedCartierModuleData j hc).nMk (m', 0) → m = m') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP.solution
