import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_coindIso_hom_eq_map_subtype_comp_map_eval_one

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.coindIso_hom_eq_map_subtype_comp_map_eval_one
    {k G : Type u} [CommRing k] [Group G] {S : Subgroup G} (A : Rep k S) (n : ℕ)
    (ev : Rep.res S.subtype (Rep.coind S.subtype A) ⟶ A)
    (hev : ∀ f : Rep.res S.subtype (Rep.coind S.subtype A), ev.hom f = (f : G → A) 1) :
    (groupCohomology.coindIso A n).hom =
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.coind S.subtype A))) n ≫
        groupCohomology.map (MonoidHom.id S) ev n := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_coindIso_hom_eq_map_subtype_comp_map_eval_one.solution
