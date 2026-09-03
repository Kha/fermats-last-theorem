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
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_endAct_actEnd_eq_map_smul_of_frobenius_eq_of_isNilpotent

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.endAct_actEnd_eq_map_smul_of_frobenius_eq_of_isNilpotent
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hB : IsNilpotent (p : B)) (X : CerednikDrinfeld.FormalODModule p B)
    (θ : CerednikDrinfeld.Zp2 p →+* WittVector p (CerednikDrinfeld.Zp2 p))
    (hθ : ∀ (a : CerednikDrinfeld.Zp2 p) (n : ℕ),
      WittVector.ghostComponent n (θ a) = (⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[n] a)
    (a : CerednikDrinfeld.Zp2 p) (ha : WittVector.frobenius a = a)
    (f : MvFormalGroup.CartierModule p X.F) :
    MvFormalGroup.CartierModule.endAct (X.actEnd a) f = WittVector.map j (θ a) • f := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_endAct_actEnd_eq_map_smul_of_frobenius_eq_of_isNilpotent.solution
