import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Flat_of_forall_isClosed_flat_stalk

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.Flat.of_forall_isClosed_flat_stalk
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [CompactSpace ↥X]
    (h : ∀ x : ↥X, IsClosed ({x} : Set ↥X) →
      letI : Algebra R ↑(X.presheaf.stalk x) :=
        (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom).toAlgebra
      Module.Flat R ↑(X.presheaf.stalk x)) :
    Flat f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Flat_of_forall_isClosed_flat_stalk.solution
