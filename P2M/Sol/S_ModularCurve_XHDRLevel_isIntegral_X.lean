import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral_pullback_toBase_of_isDomain_tensorProduct_chartAlg
import P2M.Util
namespace P2MW.S_ModularCurve_XHDRLevel_isIntegral_X

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace IntX

universe u

theorem isDomain_self_tensor (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] [IsDomain A] :
    IsDomain (R ⊗[R] A) :=
  (Algebra.TensorProduct.lid R A).toMulEquiv.isDomain

theorem nontrivial_self_tensor (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] [Nontrivial A] :
    Nontrivial (R ⊗[R] A) :=
  (Algebra.TensorProduct.lid R A).toEquiv.nontrivial

end IntX

theorem solution
    (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    IsIntegral (X p Γ hj) := by
  haveI := IntX.isDomain_self_tensor (R p) ↥(chartAlgFin p Γ hj)
  haveI := IntX.isDomain_self_tensor (R p) ↥(chartAlgInf p Γ hj)
  haveI := IntX.nontrivial_self_tensor (R p) ↥(TwoChartIntegralModel.chartAlgMid (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj))
  haveI hP : IsIntegral ↑(pullback (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (R p))))) :=
    AlgebraicCurve.TwoChartIntegralModel.isIntegral_pullback_toBase_of_isDomain_tensorProduct_chartAlg
      (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj) (R p)

  haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap (R p) (R p)))) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  exact IsIntegral.of_isIso (pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (R p)))))
