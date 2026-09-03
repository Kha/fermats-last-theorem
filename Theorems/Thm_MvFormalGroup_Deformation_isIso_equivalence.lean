import Definitions.Def_MvFormalGroup_Deformation
import P2M.Util
import P2M.Sol.S_MvFormalGroup_Deformation_isIso_equivalence

set_option autoImplicit false
theorem MvFormalGroup.Deformation.isIso_equivalence
    {S : Type} [CommRing S] {d : ℕ} (G₀ : MvFormalGroup d S) (B : Type) [CommRing B] [Algebra B S] :
    Equivalence (fun D D' : MvFormalGroup.Deformation G₀ B => D.IsIso D') := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_Deformation_isIso_equivalence.solution
