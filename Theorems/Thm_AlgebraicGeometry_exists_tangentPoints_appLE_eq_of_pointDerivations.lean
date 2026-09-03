import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_Algebra_PointDerivations
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_tangentPoints_appLE_eq_of_pointDerivations

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.exists_tangentPoints_appLE_eq_of_pointDerivations
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    (U : X.Opens) (hU : IsAffineOpen U)
    (eP : Spec (CommRingCat.of K) ⟶ (U : Scheme.{u})) (heP : eP ≫ U.ι ≫ x = 𝟙 _)
    (M : Type u) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    (D : letI := algebraOfHom x U
      ↥(Algebra.PointDerivations K Γ(X, U) ((U.topIso.inv ≫ eP.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom) M)) :
    ∃ (v : TangentPoints x (eP ≫ U.ι) M) (hv : ⊤ ≤ v.1 ⁻¹ᵁ U),
      ∀ r : Γ(X, U),
        (v.1.appLE U ⊤ hv ≫ (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K M))).hom).hom r =
          TrivSqZeroExt.inl ((U.topIso.inv ≫ eP.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom r) +
            TrivSqZeroExt.inr (D.1 r) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_tangentPoints_appLE_eq_of_pointDerivations.solution
