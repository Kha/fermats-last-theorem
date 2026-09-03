import Mathlib
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_of_free
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
namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_field
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] {K : Type u} [Field K] [CharP K p] (j : CerednikDrinfeld.Zp2 p →+* K)
    (X : CerednikDrinfeld.FormalODModule p K) (hX : X.IsSpecial j) :
    ∃ γ : Fin 2 → MvFormalGroup.CartierModule p X.F, X.IsHomogeneousVBasis j γ := by
  exact CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_of_isSpecial_of_free p j X hX
    inferInstance inferInstance
