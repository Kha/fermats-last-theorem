import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import P2M.Util
import P2M.Sol.S_MvFormalGroup_isComm_of_isComm_map_of_injective

set_option autoImplicit false

universe u

theorem MvFormalGroup.isComm_of_isComm_map_of_injective
    {g : ℕ} {R : Type u} {S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (F : MvFormalGroup g R)
    (hc : (MvFormalGroup.map φ F).IsComm) : F.IsComm := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_isComm_of_isComm_map_of_injective.solution
