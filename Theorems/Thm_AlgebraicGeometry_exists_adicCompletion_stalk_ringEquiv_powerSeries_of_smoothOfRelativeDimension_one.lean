import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_adicCompletion_stalk_ringEquiv_powerSeries_of_smoothOfRelativeDimension_one

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.exists_adicCompletion_stalk_ringEquiv_powerSeries_of_smoothOfRelativeDimension_one
    (W : Type u) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [IsAdicComplete (maximalIdeal W) W]
    [IsAlgClosed (ResidueField W)]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of W)) [SmoothOfRelativeDimension 1 f]
    (x : ↥X) (hx : f.base x = closedPoint W) (hxc : IsClosed ({x} : Set ↥X)) :
    ∃ e : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃+* PowerSeries W,
      ∀ a : W,
        e (algebraMap (X.presheaf.stalk x) _
            ((X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a)))) =
          PowerSeries.C a := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_adicCompletion_stalk_ringEquiv_powerSeries_of_smoothOfRelativeDimension_one.solution
