import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_IsDomain_tensorProduct_of_injective_algHom_laurentSeries
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_smooth_tensorProduct_chartAlgFin_of_charZero
import Theorems.Thm_Algebra_Smooth_isIntegrallyClosed_of_isDomain
import P2M.Util
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isDomain_and_isIntegrallyClosed_tensorProduct_chartAlgFin_of_le_laurentSeries
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

set_option autoImplicit false

open scoped TensorProduct
open AlgebraicCurve.TwoChartIntegralModel

universe u

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R]
    (K₀ : Type u) [Field K₀] [CharZero K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : IntermediateField K₀ (LaurentSeries K₀)) [Algebra R ↥F] [IsScalarTower R K₀ ↥F]
    (j : ↥F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set ↥F)) ↥F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set ↥F)) ↥F)
    (L : Type u) [Field L] [Algebra K₀ L] [Algebra R L] [IsScalarTower R K₀ L] :
    IsDomain (L ⊗[R] ↥(chartAlgFin R ↥F j)) ∧ IsIntegrallyClosed (L ⊗[R] ↥(chartAlgFin R ↥F j)) := by
  classical

  let φ : ↥(chartAlgFin R ↥F j) →ₐ[R] LaurentSeries K₀ :=
    { toRingHom := (F.val : ↥F →+* LaurentSeries K₀).comp ((chartAlgFin R ↥F j).val : ↥(chartAlgFin R ↥F j) →+* ↥F)
      commutes' := fun r => by
        show ((((algebraMap R ↥(chartAlgFin R ↥F j) r : ↥(chartAlgFin R ↥F j)) : ↥F)) : LaurentSeries K₀) = algebraMap R (LaurentSeries K₀) r
        rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply R K₀ ↥F r]
        show algebraMap K₀ (LaurentSeries K₀) (algebraMap R K₀ r) = algebraMap R (LaurentSeries K₀) r
        rw [HahnSeries.algebraMap_apply', HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
          PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] }
  have hφ : Function.Injective φ := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  haveI hdom : IsDomain (L ⊗[R] ↥(chartAlgFin R ↥F j)) :=
    IsDomain.tensorProduct_of_injective_algHom_laurentSeries R K₀ ↥(chartAlgFin R ↥F j) φ hφ L
  refine ⟨hdom, ?_⟩

  haveI : Algebra.Smooth K₀ (K₀ ⊗[R] ↥(chartAlgFin R ↥F j)) :=
    AlgebraicCurve.TwoChartIntegralModel.smooth_tensorProduct_chartAlgFin_of_charZero R K₀ ↥F j htj hFD hsep
  haveI : Algebra.Smooth L (L ⊗[K₀] (K₀ ⊗[R] ↥(chartAlgFin R ↥F j))) := inferInstance
  haveI : Algebra.Smooth L (L ⊗[R] ↥(chartAlgFin R ↥F j)) :=
    Algebra.Smooth.of_equiv (Algebra.TensorProduct.cancelBaseChange R K₀ L L ↥(chartAlgFin R ↥F j))
  exact Algebra.Smooth.isIntegrallyClosed_of_isDomain L (L ⊗[R] ↥(chartAlgFin R ↥F j))
