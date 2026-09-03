import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import P2M.Util
import P2M.Sol.S_Rep_shortExact_map_indFunctor

set_option autoImplicit false
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand ExtCitation

theorem Rep.shortExact_map_indFunctor
    {G : Type} [Group G] [Fintype G] (H : Subgroup G) {T₀ : ShortComplex (Rep ℤ ↥H)} (hT₀ : T₀.ShortExact) :
    (T₀.map (Rep.indFunctor ℤ H.subtype)).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_shortExact_map_indFunctor.solution
