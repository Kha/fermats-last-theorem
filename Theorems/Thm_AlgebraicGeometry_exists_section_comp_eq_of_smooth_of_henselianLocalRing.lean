import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_section_comp_eq_of_smooth_of_henselianLocalRing

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_section_comp_eq_of_smooth_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {U : Scheme.{u}} (f : U ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ U)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ σ : Spec (CommRingCat.of R) ⟶ U, σ ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ σ = x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_section_comp_eq_of_smooth_of_henselianLocalRing.solution
