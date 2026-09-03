import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_ArtinHasse
import P2M.Util
import P2M.Sol.S_MvFormalGroup_BigWittLaw_subst_addFam_frobFam

set_option autoImplicit false

universe u

theorem MvFormalGroup.BigWittLaw.subst_addFam_frobFam
    (R : Type u) [CommRing R] (n : ℕ) (hn : 0 < n) (m : ℕ) :
    MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (MvFormalGroup.BigWittLaw.frobFam R n m) =
      MvPowerSeries.subst
        (MvFormalGroup.WittLaw.pairFam (MvFormalGroup.BigWittLaw.frobFam R n))
        (MvFormalGroup.BigWittLaw.addFam R m) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_BigWittLaw_subst_addFam_frobFam.solution
