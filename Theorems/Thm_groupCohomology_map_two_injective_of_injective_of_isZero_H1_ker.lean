import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import P2M.Util
import P2M.Sol.S_groupCohomology_map_two_injective_of_injective_of_isZero_H1_ker

set_option autoImplicit false
open CategoryTheory

theorem groupCohomology.map_two_injective_of_injective_of_isZero_H1_ker {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G']
    (π : G' →* G) (hπ : Function.Surjective π)
    (C : Rep ℤ G) (C' : Rep ℤ G') (j : Rep.res π C ⟶ C') (hj : Function.Injective j.hom)
    (hjN : ∀ c' : C', (∀ g' : G', g' ∈ π.ker → C'.ρ g' c' = c') → c' ∈ Set.range j.hom)
    (h1 : CategoryTheory.Limits.IsZero (groupCohomology (Rep.res π.ker.subtype C') 1)) :
    Function.Injective (groupCohomology.map π j 2).hom := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_map_two_injective_of_injective_of_isZero_H1_ker.solution
