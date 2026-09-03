import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_map_eq_of_map_eq_zero_of_injective_of_surjective

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_map_eq_of_map_eq_zero_of_injective_of_surjective
    {k G : Type} [CommRing k] [Group G] {X₁ X₂ X₃ : Rep.{0} k G} (j : X₁ ⟶ X₂) (π : X₂ ⟶ X₃)
    (hj : Function.Injective j.hom) (hπ : Function.Surjective π.hom)
    (hexact : ∀ y : X₂.V, π.hom y = 0 ↔ y ∈ Set.range j.hom)
    (n : ℕ) (y : groupCohomology X₂ n) (hy : (groupCohomology.map (MonoidHom.id G) π n).hom y = 0) :
    ∃ x : groupCohomology X₁ n, (groupCohomology.map (MonoidHom.id G) j n).hom x = y := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_map_eq_of_map_eq_zero_of_injective_of_surjective.solution
