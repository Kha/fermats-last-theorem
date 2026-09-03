import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ker_eq_span_and_maximalIdeal_eq_of_algHom_stalk_of_smoothOfRelativeDimension_one

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

theorem AlgebraicGeometry.exists_ker_eq_span_and_maximalIdeal_eq_of_algHom_stalk_of_smoothOfRelativeDimension_one
    {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A))
    [SmoothOfRelativeDimension 1 c] (x : X)
    (π : letI : Algebra A (X.presheaf.stalk x) := ((X.presheaf.germ ⊤ x trivial).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
      X.presheaf.stalk x →ₐ[A] A) :
    letI : Algebra A (X.presheaf.stalk x) := ((X.presheaf.germ ⊤ x trivial).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
    ∃ t : X.presheaf.stalk x,
      RingHom.ker π.toRingHom = Ideal.span {t} ∧
      maximalIdeal (X.presheaf.stalk x) =
        Ideal.span {t} ⊔ (maximalIdeal A).map ((X.presheaf.germ ⊤ x trivial).hom.comp
          (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ker_eq_span_and_maximalIdeal_eq_of_algHom_stalk_of_smoothOfRelativeDimension_one.solution
