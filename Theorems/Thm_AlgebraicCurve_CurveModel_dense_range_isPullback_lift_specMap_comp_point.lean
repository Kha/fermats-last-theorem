import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_dense_range_isPullback_lift_specMap_comp_point

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.dense_range_isPullback_lift_specMap_comp_point
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type u} [Field L] [Algebra K L] (M : CurveModel K L)
    (C : Type u) [Field C] (cK : K →+* C)
    {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ M.C) (t : Y ⟶ Spec (CommRingCat.of C))
    (hY : IsPullback g t M.toBase (Spec.map (CommRingCat.ofHom cK))) :
    Dense (Set.range fun p : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _} =>
      (hY.lift (Spec.map (CommRingCat.ofHom cK) ≫ p.1) (𝟙 _)
        (by rw [Category.assoc, p.2, Category.comp_id, Category.id_comp])).base (IsLocalRing.closedPoint C)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_dense_range_isPullback_lift_specMap_comp_point.solution
