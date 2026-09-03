import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_groupCohomology_bijective_map_top_subtype

set_option autoImplicit false

open CategoryTheory
theorem groupCohomology.bijective_map_top_subtype {k G : Type} [CommRing k] [Group G] (A : Rep k G) (n : ℕ) :
    Function.Bijective (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype A)) n).hom := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_bijective_map_top_subtype.solution
