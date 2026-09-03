import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_and_forall_exists_comp_eq_of_isClosedImmersion

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_and_forall_exists_comp_eq_of_isClosedImmersion
    {R : Type} [CommRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : GoodReductionJacobian.RelativeGroupLaw R f) (hc : L.IsCommutative)
    {𝒜 : Scheme.{0}} (a : 𝒜 ⟶ Spec (CommRingCat.of R)) (ι : SchemeHomOver a f) [IsClosedImmersion ι.1]
    (hgrp : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)),
      (∃ o : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp o ι = L.one s) ∧
      (∀ x y : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
        L.mul s (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
      (∀ x : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
        L.inv s (NeronModelInfra.schemeHomOverComp x ι))) :
    ∃ L𝒜 : GoodReductionJacobian.RelativeGroupLaw R a, L𝒜.IsCommutative ∧
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s a),
        NeronModelInfra.schemeHomOverComp (L𝒜.mul s x y) ι =
          L.mul s (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
      ∀ E : SchemeHomOver f f,
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) E = L.mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E)) →
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s a),
          ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι = NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) E) →
        ∃ E' : SchemeHomOver a a,
          (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s a),
            NeronModelInfra.schemeHomOverComp (L𝒜.mul s x y) E' = L𝒜.mul s (NeronModelInfra.schemeHomOverComp x E') (NeronModelInfra.schemeHomOverComp y E')) ∧
          E'.1 ≫ ι.1 = ι.1 ≫ E.1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_and_forall_exists_comp_eq_of_isClosedImmersion.solution
