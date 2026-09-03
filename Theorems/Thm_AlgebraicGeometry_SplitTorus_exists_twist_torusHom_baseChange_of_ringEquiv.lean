import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SplitTorus_exists_twist_torusHom_baseChange_of_ringEquiv

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SplitTorus

theorem AlgebraicGeometry.SplitTorus.exists_twist_torusHom_baseChange_of_ringEquiv
    {R₀ : Type u} [CommRing R₀] {κ : Type u} [Field κ]
    (r : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R₀))
    (sbar : κ ≃+* κ) (hs : Spec.map (CommRingCat.ofHom sbar.toRingHom) ≫ r = r)
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R₀)) (L : RelativeGroupLaw R₀ g) (t : ℕ)
    (τ : SchemeHomOver (torusStr κ t) (RelativeGroupLaw.baseChangeStr r g)) :
    ∃ (Tw : pullback g r ≅ pullback g r) (τ' : SchemeHomOver (torusStr κ t) (RelativeGroupLaw.baseChangeStr r g)),

      Tw.hom ≫ pullback.fst g r = pullback.fst g r ∧
      Tw.hom ≫ pullback.snd g r = pullback.snd g r ≫ Spec.map (CommRingCat.ofHom sbar.symm.toRingHom) ∧

      τ'.1 = Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin t → ℤ) sbar.toRingHom)) ≫ τ.1 ≫ Tw.hom ∧

      ((∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
          NeronModelInfra.schemeHomOverComp (torusPtId κ t (χ * χ').ofConv) τ =
            (L.baseChange r).mul _ (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ.ofConv) τ)
              (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ'.ofConv) τ)) →
        ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
          NeronModelInfra.schemeHomOverComp (torusPtId κ t (χ * χ').ofConv) τ' =
            (L.baseChange r).mul _ (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ.ofConv) τ')
              (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ'.ofConv) τ')) ∧

      (IsClosedImmersion τ.1 → IsClosedImmersion τ'.1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SplitTorus_exists_twist_torusHom_baseChange_of_ringEquiv.solution
