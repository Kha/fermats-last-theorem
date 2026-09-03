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
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_free_lieZero_map_and_free_lieOne_map_of_isSpecial

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.exists_free_lieZero_map_and_free_lieOne_map_of_isSpecial
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (j : CerednikDrinfeld.Zp2 p →+* B) (X : CerednikDrinfeld.FormalODModule p B) (hX : X.IsSpecial j)
    (x : PrimeSpectrum B) :
    ∃ f : B, f ∉ x.asIdeal ∧
      Module.Free (Localization.Away f)
        ↥((X.map (algebraMap B (Localization.Away f))).lieZero ((algebraMap B (Localization.Away f)).comp j)) ∧
      Module.Free (Localization.Away f)
        ↥((X.map (algebraMap B (Localization.Away f))).lieOne ((algebraMap B (Localization.Away f)).comp j)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_free_lieZero_map_and_free_lieOne_map_of_isSpecial.solution
