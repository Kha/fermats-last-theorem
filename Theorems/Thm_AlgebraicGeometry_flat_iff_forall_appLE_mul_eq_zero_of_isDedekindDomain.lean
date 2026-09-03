import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain
    {R : Type u} [CommRing R] [IsDedekindDomain R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    Flat f ↔ ∀ (U : X.affineOpens) (c : R) (s : Γ(X, U)), c ≠ 0 →
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top) c * s = 0 → s = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain.solution
