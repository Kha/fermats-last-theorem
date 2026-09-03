import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_ArtinHasse
import P2M.Util
import P2M.Sol.S_MvFormalGroup_BigWittLaw_subst_pow_subst_projFam

set_option autoImplicit false

universe u

theorem MvFormalGroup.BigWittLaw.subst_pow_subst_projFam
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (f : MvPowerSeries ℕ R)
    (hf0 : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1))
        (MvPowerSeries.subst (MvFormalGroup.BigWittLaw.projFam R p) f)
      = MvPowerSeries.subst (MvFormalGroup.CartierModule.curveFam R) f := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_BigWittLaw_subst_pow_subst_projFam.solution
