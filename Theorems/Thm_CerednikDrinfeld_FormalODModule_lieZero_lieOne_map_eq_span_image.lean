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
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_lieZero_lieOne_map_eq_span_image

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.lieZero_lieOne_map_eq_span_image
    (p : ℕ) [Fact p.Prime] {B S : Type u} [CommRing B] [CommRing S] (j : CerednikDrinfeld.Zp2 p →+* B)
    (g : B →+* S) (X : CerednikDrinfeld.FormalODModule p B) :
    (Submodule.span S ((fun m : X.Lie => fun i => g (m i)) '' (X.lieZero j : Set X.Lie)) ≤
        (X.map g).lieZero (g.comp j) ∧
      Submodule.span S ((fun m : X.Lie => fun i => g (m i)) '' (X.lieOne j : Set X.Lie)) ≤
        (X.map g).lieOne (g.comp j)) ∧
    (IsCompl (X.lieZero j) (X.lieOne j) →
      Submodule.span S ((fun m : X.Lie => fun i => g (m i)) '' (X.lieZero j : Set X.Lie)) =
          (X.map g).lieZero (g.comp j) ∧
        Submodule.span S ((fun m : X.Lie => fun i => g (m i)) '' (X.lieOne j : Set X.Lie)) =
          (X.map g).lieOne (g.comp j)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_lieZero_lieOne_map_eq_span_image.solution
