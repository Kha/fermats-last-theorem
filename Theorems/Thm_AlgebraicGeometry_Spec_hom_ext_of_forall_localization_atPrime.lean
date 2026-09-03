import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Spec_hom_ext_of_forall_localization_atPrime

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Spec_hom_ext_of_forall_localization_atPrime
    {B : Type u} [CommRing B] {Z : Scheme.{u}} (f g : Spec (CommRingCat.of B) ⟶ Z)
    (h : ∀ p : PrimeSpectrum B,
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.AtPrime p.asIdeal))) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap B (Localization.AtPrime p.asIdeal))) ≫ g) :
    f = g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Spec_hom_ext_of_forall_localization_atPrime.solution
