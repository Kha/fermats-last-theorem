import Mathlib
import Definitions.Def_GroupCohomology_RepPi
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import P2M.Util
import P2M.Sol.S_GroupCohomology_RepPi_map_ihom_proj_one_injective_and_surjective

set_option autoImplicit false
open CategoryTheory

theorem GroupCohomology.RepPi.map_ihom_proj_one_injective_and_surjective
    {G : Type} [Group G] {ι : Type} [Finite ι] (X : ι → Rep ℤ G) (R : Rep ℤ G) :
    (∀ x : groupCohomology ((ihom R).obj (GroupCohomology.RepPi.obj X)) 1,
        (∀ i, (groupCohomology.map (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) 1).hom x = 0) → x = 0) ∧
    (∀ y : ∀ i, groupCohomology ((ihom R).obj (X i)) 1,
        ∃ x : groupCohomology ((ihom R).obj (GroupCohomology.RepPi.obj X)) 1,
          ∀ i, (groupCohomology.map (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) 1).hom x = y i) := by p2m_exact_reverting @_root_.P2MW.S_GroupCohomology_RepPi_map_ihom_proj_one_injective_and_surjective.solution
