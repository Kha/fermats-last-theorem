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
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X Y : CerednikDrinfeld.FormalODModule p B) (θ : X.Hom Y) (hθ : θ.IsIso)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (a : ℕ → Fin 2 → B) (ha : X.HasStructureConstants γ a) :
    Y.IsHomogeneousVBasis j (fun i => MvFormalGroup.CartierModule.map θ.toLawHom (γ i)) ∧
      Y.HasStructureConstants (fun i => MvFormalGroup.CartierModule.map θ.toLawHom (γ i)) a := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso.solution
