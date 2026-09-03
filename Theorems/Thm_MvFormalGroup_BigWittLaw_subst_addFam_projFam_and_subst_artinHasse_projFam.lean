import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_ArtinHasse
import P2M.Util
import P2M.Sol.S_MvFormalGroup_BigWittLaw_subst_addFam_projFam_and_subst_artinHasse_projFam

set_option autoImplicit false

universe u

theorem MvFormalGroup.BigWittLaw.subst_addFam_projFam_and_subst_artinHasse_projFam
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [Algebra ℤ_[p] R] :
    (∀ k : ℕ, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (MvFormalGroup.BigWittLaw.projFam R p k) =
      MvPowerSeries.subst
        (MvFormalGroup.WittLaw.pairFam (MvFormalGroup.BigWittLaw.projFam R p))
        (MvFormalGroup.WittLaw.addFam p R k)) ∧
    (∀ k : ℕ, MvPowerSeries.subst
        (fun i => (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p i)) : MvPowerSeries ℕ R))
        (MvFormalGroup.BigWittLaw.projFam R p k) = MvPowerSeries.X k) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_BigWittLaw_subst_addFam_projFam_and_subst_artinHasse_projFam.solution
