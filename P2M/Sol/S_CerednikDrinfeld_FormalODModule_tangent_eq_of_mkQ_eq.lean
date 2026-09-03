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
namespace P2MW.S_CerednikDrinfeld_FormalODModule_tangent_eq_of_mkQ_eq

set_option autoImplicit false

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X : CerednikDrinfeld.FormalODModule p B) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (m m' : MvFormalGroup.CartierModule p X.F)
    (h : (X.toGradedCartierModuleData j hc).vRange.mkQ m = (X.toGradedCartierModuleData j hc).vRange.mkQ m') :
    MvFormalGroup.CartierModule.tangent m = MvFormalGroup.CartierModule.tangent m' := by

  have hmem : m - m' ∈ (X.toGradedCartierModuleData j hc).vRange := (Submodule.Quotient.eq _).mp h
  obtain ⟨y, hy⟩ := ((X.toGradedCartierModuleData j hc).mem_vRange_iff _).mp hmem
  have hV : MvFormalGroup.CartierModule.tangent (MvFormalGroup.CartierModule.verschiebungInt y) = 0 :=
    MvFormalGroup.CartierModule.tangent_verschiebungInt y
  have hy' : MvFormalGroup.CartierModule.verschiebungInt y = m - m' := by
    rw [← CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_verschiebung_apply X j hc y]; exact hy
  rw [hy', map_sub, sub_eq_zero] at hV
  exact hV
