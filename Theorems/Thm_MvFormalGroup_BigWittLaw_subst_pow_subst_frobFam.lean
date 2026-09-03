import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_ArtinHasse
import P2M.Util
import P2M.Sol.S_MvFormalGroup_BigWittLaw_subst_pow_subst_frobFam

set_option autoImplicit false

universe u

theorem MvFormalGroup.BigWittLaw.subst_pow_subst_frobFam
    (R : Type u) [CommRing R] (n : ℕ) (hn : 0 < n) (G : MvPowerSeries ℕ R)
    (hG0 : MvPowerSeries.constantCoeff G = 0) :
    MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1))
        (MvPowerSeries.subst (MvFormalGroup.BigWittLaw.frobFam R n) G)
      = MvPowerSeries.expand n hn.ne'
          (MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) G) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_BigWittLaw_subst_pow_subst_frobFam.solution
