import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_ArtinHasse
import P2M.Util
import P2M.Sol.S_MvFormalGroup_ArtinHasse_subst_addFam_map_coord

set_option autoImplicit false

universe u

theorem MvFormalGroup.ArtinHasse.subst_addFam_map_coord
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [Algebra ℤ_[p] R] (n : ℕ) :
    MvPowerSeries.subst (MvFormalGroup.WittLaw.addFam p R)
        (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p n)) : MvPowerSeries ℕ R) =
      MvPowerSeries.subst
        (MvFormalGroup.WittLaw.pairFam fun m =>
          (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p m)) : MvPowerSeries ℕ R))
        (MvFormalGroup.BigWittLaw.addFam R n) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_ArtinHasse_subst_addFam_map_coord.solution
