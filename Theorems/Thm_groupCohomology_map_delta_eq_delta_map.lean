import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_map_delta_eq_delta_map
set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.map_delta_eq_delta_map
    {k G G' : Type} [CommRing k] [Group G] [Group G'] (π : G' →* G)
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact) {X' : ShortComplex (Rep k G')} (hX' : X'.ShortExact)
    (φ₁ : Rep.res π X.X₁ ⟶ X'.X₁) (φ₂ : Rep.res π X.X₂ ⟶ X'.X₂) (φ₃ : Rep.res π X.X₃ ⟶ X'.X₃)
    (w₁ : (Rep.resFunctor π).map X.f ≫ φ₂ = φ₁ ≫ X'.f) (w₂ : (Rep.resFunctor π).map X.g ≫ φ₃ = φ₂ ≫ X'.g)
    (i j : ℕ) (hij : i + 1 = j) (y : groupCohomology X.X₃ i) :
    (groupCohomology.map π φ₁ j).hom ((groupCohomology.δ hX i j hij).hom y) =
      (groupCohomology.δ hX' i j hij).hom ((groupCohomology.map π φ₃ i).hom y) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_map_delta_eq_delta_map.solution
