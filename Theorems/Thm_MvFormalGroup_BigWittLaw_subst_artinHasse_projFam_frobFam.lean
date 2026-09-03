import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_ArtinHasse
import P2M.Util
import P2M.Sol.S_MvFormalGroup_BigWittLaw_subst_artinHasse_projFam_frobFam

set_option autoImplicit false

universe u

theorem MvFormalGroup.BigWittLaw.subst_artinHasse_projFam_frobFam
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [Algebra ℤ_[p] R] :
    (∀ m : ℕ, (¬ ∃ k : ℕ, m = p ^ k) → ∀ k : ℕ,
      MvPowerSeries.subst
        (fun i => MvPowerSeries.subst (MvFormalGroup.BigWittLaw.projFam R p)
          ((↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p i)) : MvPowerSeries ℕ R)))
        (MvFormalGroup.BigWittLaw.frobFam R m k) = 0) ∧
    (∀ k : ℕ,
      MvPowerSeries.subst
        (fun i => MvPowerSeries.subst (MvFormalGroup.BigWittLaw.projFam R p)
          ((↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p i)) : MvPowerSeries ℕ R)))
        (MvFormalGroup.BigWittLaw.frobFam R p k)
      = MvPowerSeries.subst (MvFormalGroup.BigWittLaw.frobFam R p)
          (MvPowerSeries.subst (MvFormalGroup.BigWittLaw.projFam R p)
            ((↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p k)) : MvPowerSeries ℕ R)))) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_BigWittLaw_subst_artinHasse_projFam_frobFam.solution
