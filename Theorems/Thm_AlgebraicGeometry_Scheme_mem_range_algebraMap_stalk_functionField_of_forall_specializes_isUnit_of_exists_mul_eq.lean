import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_mem_range_algebraMap_stalk_functionField_of_forall_specializes_isUnit_of_exists_mul_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.mem_range_algebraMap_stalk_functionField_of_forall_specializes_isUnit_of_exists_mul_eq
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (CommRingCat.of R)) (r : R) (x : X)

    (hprime : (Ideal.span {(X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))}).IsPrime)
    (hne : (X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) ≠ 0)
    (f : X.functionField)

    (h1 : ∃ a b : X.presheaf.stalk x,
      b ∉ Ideal.span {(X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))} ∧
      f * algebraMap (X.presheaf.stalk x) X.functionField b = algebraMap (X.presheaf.stalk x) X.functionField a)

    (h2 : ∀ P : X, P ⤳ x →
      IsUnit ((X.presheaf.germ ⊤ P trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) →
      f ∈ Set.range (algebraMap (X.presheaf.stalk P) X.functionField)) :
    f ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_mem_range_algebraMap_stalk_functionField_of_forall_specializes_isUnit_of_exists_mul_eq.solution
