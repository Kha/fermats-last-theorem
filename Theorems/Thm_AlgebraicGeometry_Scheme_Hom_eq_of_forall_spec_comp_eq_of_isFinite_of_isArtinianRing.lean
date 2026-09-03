import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_spec_comp_eq_of_isFinite_of_isArtinianRing

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory

theorem AlgebraicGeometry.Scheme.Hom.eq_of_forall_spec_comp_eq_of_isFinite_of_isArtinianRing
    {T : Type} [CommRing T] [IsArtinianRing T] {Z Y : Scheme} (p : Z ⟶ Spec (CommRingCat.of T)) [IsFinite p]
    (g h : Z ⟶ Y)
    (H : ∀ (B : Type) [CommRing B] [IsArtinianRing B] [IsLocalRing B] (z : Spec (CommRingCat.of B) ⟶ Z), z ≫ g = z ≫ h) :
    g = h := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_spec_comp_eq_of_isFinite_of_isArtinianRing.solution
