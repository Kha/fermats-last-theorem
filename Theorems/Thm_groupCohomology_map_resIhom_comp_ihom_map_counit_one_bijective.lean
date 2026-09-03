import Mathlib
import Definitions.Def_GroupCohomology_RepPi
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import P2M.Util
import P2M.Sol.S_groupCohomology_map_resIhom_comp_ihom_map_counit_one_bijective

set_option autoImplicit false
open CategoryTheory

theorem groupCohomology.map_resIhom_comp_ihom_map_counit_one_bijective
    {G : Type} [Group G] (D : Subgroup G) (R : Rep ℤ G) (Y : Rep ℤ ↥D) :
    Function.Bijective (groupCohomology.map D.subtype
      (Rep.resIhom D.subtype R (Rep.coind D.subtype Y) ≫
        (ihom (Rep.res D.subtype R)).map ((Rep.resCoindAdjunction ℤ D.subtype).counit.app Y)) 1).hom := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_map_resIhom_comp_ihom_map_counit_one_bijective.solution
