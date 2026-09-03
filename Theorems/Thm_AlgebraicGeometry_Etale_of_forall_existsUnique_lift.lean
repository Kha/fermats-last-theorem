import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Etale_of_forall_existsUnique_lift

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Etale.of_forall_existsUnique_lift
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (hlift : ∀ (R S : Type u) [CommRing R] [CommRing S] (φ : R →+* S), Function.Surjective φ →
      RingHom.ker φ ^ 2 = ⊥ → ∀ (a : Spec (CommRingCat.of S) ⟶ X) (b : Spec (CommRingCat.of R) ⟶ Y),
        a ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ b →
        ∃! l : Spec (CommRingCat.of R) ⟶ X, Spec.map (CommRingCat.ofHom φ) ≫ l = a ∧ l ≫ f = b) :
    Etale f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Etale_of_forall_existsUnique_lift.solution
