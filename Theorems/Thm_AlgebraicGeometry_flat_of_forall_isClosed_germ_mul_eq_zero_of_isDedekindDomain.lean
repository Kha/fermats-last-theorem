import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_flat_of_forall_isClosed_germ_mul_eq_zero_of_isDedekindDomain

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry~flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain"

theorem AlgebraicGeometry.flat_of_forall_isClosed_germ_mul_eq_zero_of_isDedekindDomain
    {R : Type u} [CommRing R] [IsDedekindDomain R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f]
    (h : ∀ x : X, IsClosed ({x} : Set X) → (f x).asIdeal ≠ ⊥ →
      ∀ (c : R) (z : X.presheaf.stalk x), c ≠ 0 →
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial) c * z = 0 → z = 0) :
    Flat f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_flat_of_forall_isClosed_germ_mul_eq_zero_of_isDedekindDomain.solution
