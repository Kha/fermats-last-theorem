import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_section_comp_eq_of_etale_of_henselianLocalRing

open CategoryTheory

universe u

theorem AlgebraicGeometry.exists_section_comp_eq_of_etale_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [AlgebraicGeometry.Etale f]
    (e : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ X)
    (he : e ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ s = e := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_section_comp_eq_of_etale_of_henselianLocalRing.solution
