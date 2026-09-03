import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_map_coindFunctor_map_comp_coindIso_hom

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.map_coindFunctor_map_comp_coindIso_hom
    {k G : Type u} [CommRing k] [Group G] {S : Subgroup G} {A B : Rep k S} (φ : A ⟶ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) ((Rep.coindFunctor k S.subtype).map φ) n ≫
        (groupCohomology.coindIso B n).hom =
      (groupCohomology.coindIso A n).hom ≫ groupCohomology.map (MonoidHom.id S) φ n := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_map_coindFunctor_map_comp_coindIso_hom.solution
