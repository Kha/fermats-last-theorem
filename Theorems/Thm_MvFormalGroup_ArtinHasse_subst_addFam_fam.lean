import Mathlib
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_ArtinHasse
import P2M.Util
import P2M.Sol.S_MvFormalGroup_ArtinHasse_subst_addFam_fam

set_option autoImplicit false

universe u

theorem MvFormalGroup.ArtinHasse.subst_addFam_fam
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [CharP R p] (n : ℕ) :
    MvPowerSeries.subst (MvFormalGroup.WittLaw.addFam p R) (MvFormalGroup.ArtinHasse.fam p R n) =
      MvPowerSeries.subst (MvFormalGroup.WittLaw.pairFam (MvFormalGroup.ArtinHasse.fam p R))
        (MvFormalGroup.BigWittLaw.addFam R n) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_ArtinHasse_subst_addFam_fam.solution
