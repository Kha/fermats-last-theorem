import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import P2M.Util
namespace P2MW.S_Rep_shortExact_map_indFunctor

set_option autoImplicit false
set_option maxHeartbeats 3200000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand ExtCitation

open CategoryTheory.Limits in
theorem solution
    {G : Type} [Group G] [Fintype G] (H : Subgroup G) {T₀ : ShortComplex (Rep ℤ ↥H)} (hT₀ : T₀.ShortExact) :
    (T₀.map (Rep.indFunctor ℤ H.subtype)).ShortExact := by
  classical
  haveI : H.FiniteIndex := inferInstance
  haveI : PreservesLimitsOfSize.{0, 0} (Rep.indFunctor ℤ H.subtype) := (Rep.resIndAdjunction ℤ H).rightAdjoint_preservesLimits
  haveI : PreservesColimitsOfSize.{0, 0} (Rep.indFunctor ℤ H.subtype) := (Rep.indResAdjunction ℤ H.subtype).leftAdjoint_preservesColimits
  exact hT₀.map_of_exact (Rep.indFunctor ℤ H.subtype)
