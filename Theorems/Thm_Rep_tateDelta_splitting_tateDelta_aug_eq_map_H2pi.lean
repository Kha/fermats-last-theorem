import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_SplittingModule
import P2M.Util
import P2M.Sol.S_Rep_tateDelta_splitting_tateDelta_aug_eq_map_H2pi

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.tateDelta_splitting_tateDelta_aug_eq_map_H2pi {k G : Type u} [CommRing k] [Group G]
    (C : Rep.{u} k G) (φ : groupCohomology.cocycles₂ C) (S : Subgroup G) [Fintype S]
    (hE : ((Rep.augShortComplex k G).map (Rep.resFunctor S.subtype)).ShortExact)
    (hF : ((Rep.splittingShortComplex C φ).map (Rep.resFunctor S.subtype)).ShortExact)
    (e : (Rep.res S.subtype (Rep.trivial k G k)).ρ.invariants) (he : (e : k) = 1) :
    (Rep.tateδ hF 1).hom ((Rep.tateδ hE 0).hom
        (Submodule.Quotient.mk e : (Rep.res S.subtype (Rep.trivial k G k)).tateH0))
      = (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom (groupCohomology.H2π C φ) := by p2m_exact_reverting @_root_.P2MW.S_Rep_tateDelta_splitting_tateDelta_aug_eq_map_H2pi.solution
