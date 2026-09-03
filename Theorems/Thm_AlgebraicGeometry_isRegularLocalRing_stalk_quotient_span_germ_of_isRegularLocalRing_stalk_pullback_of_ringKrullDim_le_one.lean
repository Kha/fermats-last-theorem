import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isRegularLocalRing_stalk_quotient_span_germ_of_isRegularLocalRing_stalk_pullback_of_ringKrullDim_le_one

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isRegularLocalRing_stalk_quotient_span_germ_of_isRegularLocalRing_stalk_pullback_of_ringKrullDim_le_one
    {A : Type u} [CommRing A] (ϖ : A) (hmax : (Ideal.span {ϖ} : Ideal A).IsMaximal)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (K' : Type u) [Field K'] [Algebra A K'] (hϖ : algebraMap A K' ϖ = 0)
    (z' : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap A K')))))
    (hreg : IsRegularLocalRing
      ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap A K')))).presheaf.stalk z'))
    (hdim : ringKrullDim
      ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap A K')))).presheaf.stalk z') ≤ 1) :
    IsRegularLocalRing
      ((X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A K')))).base z')) ⧸
        Ideal.span {((X.presheaf.germ ⊤ ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A K')))).base z')
            trivial).hom ((f.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))}) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isRegularLocalRing_stalk_quotient_span_germ_of_isRegularLocalRing_stalk_pullback_of_ringKrullDim_le_one.solution
