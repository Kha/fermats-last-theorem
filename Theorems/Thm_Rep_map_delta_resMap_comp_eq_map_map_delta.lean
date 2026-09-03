import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import P2M.Util
import P2M.Sol.S_Rep_map_delta_resMap_comp_eq_map_map_delta

set_option autoImplicit false
open CategoryTheory

theorem Rep.map_delta_resMap_comp_eq_map_map_delta {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G']
    (π : G' →* G) (C : Rep ℤ G) (C' : Rep ℤ G') (j : Rep.res π C ⟶ C')
    (B : Rep ℤ G) [Fintype B]
    (hX : (Rep.relationSeqInt B).ShortExact) (hX' : (Rep.relationSeqInt (Rep.res π B)).ShortExact)
    (φ : Rep.relationModuleInt B ⟶ C) (y : groupCohomology B 1) :
    (groupCohomology.map (MonoidHom.id G')
        (Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map φ ≫ j) 2).hom
      ((groupCohomology.δ hX' 1 2 rfl).hom ((groupCohomology.map π (𝟙 (Rep.res π B)) 1).hom y)) =
    (groupCohomology.map π j 2).hom
      ((groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y)) := by p2m_exact_reverting @_root_.P2MW.S_Rep_map_delta_resMap_comp_eq_map_map_delta.solution
