import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_linearMap_apply_eq_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm_of_infinite
import Theorems.Thm_NumberField_InfiniteAdeleRing_map_linearMap_eq_inv_prod_norm_archEval_det_pow_mult_smul_of_isAddHaarMeasure
import P2M.Util
namespace P2MW.S_AutomorphicForm_map_mul_sigmaTensor_sub_mul_addHaar_infiniteAdeleRing_eq_inv_prod_norm_archEval_algebraNorm_sub_pow_mult_smul

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (a b : (L ⊗[K] InfiniteAdeleRing K))
    (hab : IsUnit (Algebra.norm (InfiniteAdeleRing K) a - Algebra.norm (InfiniteAdeleRing K) b)) :
    Measure.map (fun y : (L ⊗[K] InfiniteAdeleRing K) => a * AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - b * y) lam =
        ENNReal.ofReal ((∏ w : NumberField.InfinitePlace K, ‖NumberField.AdelicLevel.archEval K w (Algebra.norm (InfiniteAdeleRing K) a - Algebra.norm (InfiniteAdeleRing K) b)‖ ^ w.mult)⁻¹) • lam ∧
    ∀ g : (L ⊗[K] InfiniteAdeleRing K) → ℂ,
      ∫ y, g (a * AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - b * y) ∂lam =
        (((∏ w : NumberField.InfinitePlace K, ‖NumberField.AdelicLevel.archEval K w (Algebra.norm (InfiniteAdeleRing K) a - Algebra.norm (InfiniteAdeleRing K) b)‖ ^ w.mult)⁻¹ : ℝ) : ℂ) * ∫ y, g y ∂lam := by
  classical

  obtain ⟨T, hT, hdet⟩ :=
    AutomorphicForm.exists_linearMap_apply_eq_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm_of_infinite K L σ hgen (InfiniteAdeleRing K) a b
  have hfun : (fun y : (L ⊗[K] InfiniteAdeleRing K) => a * AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - b * y) = ⇑T :=
    funext fun y => (hT y).symm

  have hunit : IsUnit (LinearMap.det T) := by
    rw [hdet]
    refine (isUnit_one.neg.pow _).mul ?_
    have : Algebra.norm (InfiniteAdeleRing K) b - Algebra.norm (InfiniteAdeleRing K) a =
        -(Algebra.norm (InfiniteAdeleRing K) a - Algebra.norm (InfiniteAdeleRing K) b) := by ring
    rw [this]; exact hab.neg

  have hnorm : ∀ w : NumberField.InfinitePlace K,
      ‖NumberField.AdelicLevel.archEval K w (LinearMap.det T)‖ =
        ‖NumberField.AdelicLevel.archEval K w (Algebra.norm (InfiniteAdeleRing K) a - Algebra.norm (InfiniteAdeleRing K) b)‖ := by
    intro w
    rw [hdet, map_mul, map_pow, map_neg, map_one, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      ← norm_neg, ← map_neg]
    congr 2; ring
  have hmap := NumberField.InfiniteAdeleRing.map_linearMap_eq_inv_prod_norm_archEval_det_pow_mult_smul_of_isAddHaarMeasure
    K (L ⊗[K] InfiniteAdeleRing K) lam T hunit
  simp only [hnorm] at hmap
  refine ⟨by rw [hfun]; exact hmap, fun g => ?_⟩

  obtain ⟨u, hu⟩ := (LinearMap.isUnit_iff_isUnit_det T).mpr hunit
  haveI : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  have hc1 : Continuous ((u : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K)) : (L ⊗[K] InfiniteAdeleRing K) → (L ⊗[K] InfiniteAdeleRing K)) :=
    IsModuleTopology.continuous_of_linearMap _
  have hc2 : Continuous ((↑(u⁻¹) : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K)) : (L ⊗[K] InfiniteAdeleRing K) → (L ⊗[K] InfiniteAdeleRing K)) :=
    IsModuleTopology.continuous_of_linearMap _
  let Te : (L ⊗[K] InfiniteAdeleRing K) ≃ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K) := LinearMap.GeneralLinearGroup.toLinearEquiv u
  have hTe : ∀ y, Te y = T y := fun y => by
    show (u : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K)) y = T y
    rw [hu]
  let H : (L ⊗[K] InfiniteAdeleRing K) ≃ₜ (L ⊗[K] InfiniteAdeleRing K) :=
    { toEquiv := Te.toEquiv
      continuous_toFun := hc1
      continuous_invFun := hc2 }
  have hHT : (H : (L ⊗[K] InfiniteAdeleRing K) → (L ⊗[K] InfiniteAdeleRing K)) = ⇑T := funext fun y => hTe y
  have h1 := MeasureTheory.integral_map_equiv (μ := lam) H.toMeasurableEquiv g
  rw [Homeomorph.toMeasurableEquiv_coe, hHT, ← hfun] at h1
  rw [← h1, hfun, hmap, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
