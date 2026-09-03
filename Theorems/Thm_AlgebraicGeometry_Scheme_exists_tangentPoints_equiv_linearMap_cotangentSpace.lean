import Mathlib
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_tangentPoints_equiv_linearMap_cotangentSpace

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_tangentPoints_equiv_linearMap_cotangentSpace
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    (pt : Spec (CommRingCat.of K) ⟶ X) (hpt : pt ≫ x = 𝟙 (Spec (CommRingCat.of K))) :
    letI : Algebra K (X.presheaf.stalk (pt.base (IsLocalRing.closedPoint K))) :=
      ((X.presheaf.germ ⊤ (pt.base (IsLocalRing.closedPoint K)) trivial).hom.comp
        (x.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
    ∃ γ : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V],
        TangentPoints x pt V ≃
          (IsLocalRing.CotangentSpace (X.presheaf.stalk (pt.base (IsLocalRing.closedPoint K))) →ₗ[K] V),
      ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
        (W : Type u) [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
        (φ : V →ₗ[K] W) (v : TangentPoints x pt V),
        γ W (v.map φ) = φ ∘ₗ γ V v := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_tangentPoints_equiv_linearMap_cotangentSpace.solution
