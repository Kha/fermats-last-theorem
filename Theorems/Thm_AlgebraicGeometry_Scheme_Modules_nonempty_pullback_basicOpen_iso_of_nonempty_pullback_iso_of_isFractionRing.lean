import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_basicOpen_iso_of_nonempty_pullback_iso_of_isFractionRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_basicOpen_iso_of_nonempty_pullback_iso_of_isFractionRing
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (KK : Type) [Field KK] [Algebra R KK] [IsFractionRing R KK]
    {X XK : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (fK : XK ⟶ Spec (CommRingCat.of KK)) (gK : XK ⟶ X) (hgK : IsPullback gK fK f (Spec.map (CommRingCat.ofHom (algebraMap R KK))))
    (M M' : X.Modules) (h : Nonempty ((Scheme.Modules.pullback gK).obj M ≅ (Scheme.Modules.pullback gK).obj M')) :
    (∀ x : X, x ∈ X.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ)) ↔ f.base x ≠ IsLocalRing.closedPoint R) ∧
      Nonempty ((Scheme.Modules.pullback (X.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ))).ι).obj M ≅
        (Scheme.Modules.pullback (X.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ))).ι).obj M') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_basicOpen_iso_of_nonempty_pullback_iso_of_isFractionRing.solution
