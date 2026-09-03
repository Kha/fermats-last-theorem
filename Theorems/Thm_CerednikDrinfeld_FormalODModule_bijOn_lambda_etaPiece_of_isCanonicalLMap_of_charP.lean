import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_bijOn_lambda_etaPiece_of_isCanonicalLMap_of_charP

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.FormalODModule.bijOn_lambda_etaPiece_of_isCanonicalLMap_of_charP
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (X : FormalODModule p B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (n : Fin 2)
    (hsurj : ∀ z ∈ X.gradedPiece j ((n + 1 : Fin 2) : ℕ), ∃ m ∈ X.gradedPiece j (n : ℕ),
      ∃ m' : MvFormalGroup.CartierModule p X.F, z = MvFormalGroup.CartierModule.endAct X.varpiEnd m + MvFormalGroup.CartierModule.verschiebungInt m')
    (hinj : ∀ m ∈ X.gradedPiece j (n : ℕ),
      (∃ g : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.verschiebungInt g = MvFormalGroup.CartierModule.endAct X.varpiEnd m) →
        ∃ g' : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.verschiebungInt g' = m) :
    Set.BijOn (X.toGradedCartierModuleData j hc).lambda
      ((X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung n : Set _)
      {m : MvFormalGroup.CartierModule p X.F | m ∈ X.gradedPiece j ((n + 1 : Fin 2) : ℕ) ∧ MvFormalGroup.CartierModule.endAct X.varpiEnd m = MvFormalGroup.CartierModule.verschiebungInt m} := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_bijOn_lambda_etaPiece_of_isCanonicalLMap_of_charP.solution
