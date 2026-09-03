import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_BigWittLaw
import P2M.Util
import P2M.Sol.S_MvFormalGroup_BigWittLaw_subst_addFam_verschiebungFam

set_option autoImplicit false

universe u

theorem MvFormalGroup.BigWittLaw.subst_addFam_verschiebungFam
    (R : Type u) [CommRing R] (n : ℕ) (hn : 0 < n) (k : ℕ) :
    MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R)
        ((if n ∣ k + 1 then MvPowerSeries.X ((k + 1) / n - 1) else 0) : MvPowerSeries ℕ R) =
      MvPowerSeries.subst
        (MvFormalGroup.WittLaw.pairFam fun j =>
          ((if n ∣ j + 1 then MvPowerSeries.X ((j + 1) / n - 1) else 0) : MvPowerSeries ℕ R))
        (MvFormalGroup.BigWittLaw.addFam R k) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_BigWittLaw_subst_addFam_verschiebungFam.solution
