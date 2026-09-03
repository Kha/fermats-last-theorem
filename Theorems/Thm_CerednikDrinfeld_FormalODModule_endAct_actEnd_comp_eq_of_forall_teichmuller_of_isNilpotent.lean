import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_endAct_actEnd_comp_eq_of_forall_teichmuller_of_isNilpotent

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.FormalODModule.endAct_actEnd_comp_eq_of_forall_teichmuller_of_isNilpotent
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (hB : IsNilpotent (p : B))
    (X X' : FormalODModule p B)
    (θ : MvFormalGroup.CartierModule p X.F →+ MvFormalGroup.CartierModule p X'.F)
    (hθ : ∀ (c : GaloisField p 2) (f : MvFormalGroup.CartierModule p X.F),
      θ (MvFormalGroup.CartierModule.endAct (X.actEnd (WittVector.teichmuller p c)) f) =
        MvFormalGroup.CartierModule.endAct (X'.actEnd (WittVector.teichmuller p c)) (θ f)) :
    ∀ (a : Zp2 p) (f : MvFormalGroup.CartierModule p X.F),
      θ (MvFormalGroup.CartierModule.endAct (X.actEnd a) f) =
        MvFormalGroup.CartierModule.endAct (X'.actEnd a) (θ f) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_endAct_actEnd_comp_eq_of_forall_teichmuller_of_isNilpotent.solution
