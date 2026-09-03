import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_stalk_flat_and_maximalIdeal_eq_sup_span_of_smoothOfRelativeDimension_one

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.stalk_flat_and_maximalIdeal_eq_sup_span_of_smoothOfRelativeDimension_one
    (W : Type u) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [IsAdicComplete (maximalIdeal W) W]
    [IsAlgClosed (ResidueField W)]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of W)) [SmoothOfRelativeDimension 1 f]
    (x : ↥X) (hx : f.base x = closedPoint W) (hxc : IsClosed ({x} : Set ↥X)) :
    letI : Algebra W (X.presheaf.stalk x) :=
      ((X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom)).toAlgebra
    IsNoetherianRing (X.presheaf.stalk x) ∧ IsLocalHom (algebraMap W (X.presheaf.stalk x)) ∧
      Module.Flat W (X.presheaf.stalk x) ∧
      Function.Surjective ((IsLocalRing.residue (X.presheaf.stalk x)).comp (algebraMap W (X.presheaf.stalk x))) ∧
      ∃ t : X.presheaf.stalk x,
        maximalIdeal (X.presheaf.stalk x) = (maximalIdeal W).map (algebraMap W (X.presheaf.stalk x)) ⊔ Ideal.span {t} ∧
        ringKrullDim (X.presheaf.stalk x ⧸ (maximalIdeal W).map (algebraMap W (X.presheaf.stalk x))) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_stalk_flat_and_maximalIdeal_eq_sup_span_of_smoothOfRelativeDimension_one.solution
