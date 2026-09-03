import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_exists_varpiEnd_eq_verschiebungInt_of_charP

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_exists_varpiEnd_eq_verschiebungInt_of_charP
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (X : FormalODModule p B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (hV : Function.Injective (MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := X.F)))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (i : Fin 2) (hi : ∀ m ∈ X.gradedPiece j (i : ℕ),
      ∃ g : MvFormalGroup.CartierModule p X.F,
        MvFormalGroup.CartierModule.verschiebungInt g = MvFormalGroup.CartierModule.endAct X.varpiEnd m)
    (z : (X.toGradedCartierModuleData j hc).NMod) :
    z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i ↔
      ∃ m : MvFormalGroup.CartierModule p X.F, m ∈ X.gradedPiece j (i : ℕ) ∧
        MvFormalGroup.CartierModule.endAct X.varpiEnd m = MvFormalGroup.CartierModule.verschiebungInt m ∧
        z = (X.toGradedCartierModuleData j hc).nMk (m, 0) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_exists_varpiEnd_eq_verschiebungInt_of_charP.solution
