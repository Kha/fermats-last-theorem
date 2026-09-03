import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
namespace P2MW.S_WeierstrassProjModel_isOriginChartSection_kwZeroSect_kwYChartEval

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

open HomogeneousLocalization in
theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T) :
    IsOriginChartSection (kwZeroSect T W.toAffine) (kwYChartEval T W.toAffine) ∧
      kwYChartEval T W.toAffine (xOverY W) = 0 ∧ kwYChartEval T W.toAffine (zOverY W) = 0 := by

  have hval : ∀ (i : Fin 3),
      kwYChartEval T W.toAffine (Away.mk (projModelGradingCR W) (coord_mem W 1) 1 (coord W i)
        (by simpa using coord_mem W i)) = MvPolynomial.eval ![(0 : T), 1, 0] (MvPolynomial.X i) := by
    intro i
    unfold kwYChartEval
    rw [RingHom.comp_apply]
    have hv : (algebraMap (Away (projModelGradingCR W) (coord W 1))
        (Localization.Away (coord W 1)))
        (Away.mk (projModelGradingCR W) (coord_mem W 1) 1 (coord W i) (by simpa using coord_mem W i)) =
        IsLocalization.mk' (Localization.Away (coord W 1)) (coord W i)
          (⟨coord W 1 ^ 1, 1, rfl⟩ : Submonoid.powers (coord W 1)) := by
      rw [HomogeneousLocalization.algebraMap_apply, Away.val_mk, Localization.mk_eq_mk']
    rw [hv, IsLocalization.Away.lift, IsLocalization.lift_mk']
    simp only [pow_one, map_one]
    rw [Units.mul_inv_eq_iff_eq_mul]
    change kwYEvalRingHom T W.toAffine (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      _ * kwYEvalRingHom T W.toAffine (Ideal.Quotient.mk _ (MvPolynomial.X 1))
    rw [kwYEvalRingHom_mk_X1, mul_one]
    rfl
  refine ⟨rfl, ?_, ?_⟩
  · change kwYChartEval T W.toAffine (Away.mk _ (coord_mem W 1) 1 (coord W 0) _) = 0
    rw [hval 0]; simp
  · change kwYChartEval T W.toAffine (Away.mk _ (coord_mem W 1) 1 (coord W 2) _) = 0
    rw [hval 2]; simp
