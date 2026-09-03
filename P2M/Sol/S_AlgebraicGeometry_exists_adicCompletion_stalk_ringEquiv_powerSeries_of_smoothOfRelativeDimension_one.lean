import Mathlib
import Theorems.Thm_IsLocalRing_exists_ringEquiv_adicCompletion_powerSeries_of_flat_of_maximalIdeal_eq_sup_span
import Theorems.Thm_AlgebraicGeometry_stalk_flat_and_maximalIdeal_eq_sup_span_of_smoothOfRelativeDimension_one
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_exists_adicCompletion_stalk_ringEquiv_powerSeries_of_smoothOfRelativeDimension_one

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem solution
    (W : Type u) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [IsAdicComplete (maximalIdeal W) W]
    [IsAlgClosed (ResidueField W)]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of W)) [SmoothOfRelativeDimension 1 f]
    (x : ↥X) (hx : f.base x = closedPoint W) (hxc : IsClosed ({x} : Set ↥X)) :
    ∃ e : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃+* PowerSeries W,
      ∀ a : W,
        e (algebraMap (X.presheaf.stalk x) _
            ((X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a)))) =
          PowerSeries.C a := by
  letI inst : Algebra W (X.presheaf.stalk x) :=
    ((X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom)).toAlgebra
  obtain ⟨hN, hloc, hflat, hres, t, ht, hdim⟩ :=
    AlgebraicGeometry.stalk_flat_and_maximalIdeal_eq_sup_span_of_smoothOfRelativeDimension_one W f x hx hxc
  haveI := hN; haveI := hloc; haveI := hflat
  obtain ⟨e, he, -⟩ :=
    IsLocalRing.exists_ringEquiv_adicCompletion_powerSeries_of_flat_of_maximalIdeal_eq_sup_span
      W (X.presheaf.stalk x) hres t ht hdim
  exact ⟨e, fun a => he a⟩
