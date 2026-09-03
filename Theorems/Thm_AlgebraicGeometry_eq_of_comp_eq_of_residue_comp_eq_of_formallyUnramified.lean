import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
theorem AlgebraicGeometry.eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified
    {X Y : Scheme.{u}} (g : X ⟶ Y) [FormallyUnramified g] [LocallyOfFiniteType g]
    (A : Type u) [CommRing A] [IsLocalRing A]
    (u₁ u₂ : Spec (CommRingCat.of A) ⟶ X) (hg : u₁ ≫ g = u₂ ≫ g)
    (hres : Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ u₁ =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ u₂) :
    u₁ = u₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified.solution
