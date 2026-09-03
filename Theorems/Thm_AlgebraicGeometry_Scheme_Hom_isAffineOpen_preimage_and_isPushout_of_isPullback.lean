import Mathlib
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (U : Y.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (φ ⁻¹ᵁ U) ∧
      letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra (φ ⁻¹ᵁ U)
      letI : Algebra Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
      ∀ [Algebra A Γ(X, φ ⁻¹ᵁ U)] [IsScalarTower A B Γ(X, φ ⁻¹ᵁ U)]
        [IsScalarTower A Γ(Y, U) Γ(X, φ ⁻¹ᵁ U)],
        Algebra.IsPushout A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback.solution
