import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_linearMap_prod_norm_pow_mul_integral_comp_sigmaTensor_sub_mul_twistedLogWeight_eq_add_sum

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.exists_linearMap_prod_norm_pow_mul_integral_comp_sigmaTensor_sub_mul_twistedLogWeight_eq_add_sum
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (w : NumberField.InfinitePlace K)
    (r : L ⊗[K] InfiniteAdeleRing K) (c : (InfiniteAdeleRing K)ˣ)
    (hc : (c : InfiniteAdeleRing K) = 1 - Algebra.norm (InfiniteAdeleRing K) r)
    (Ψ : NumberField.mixedEmbedding.mixedSpace L → ℂ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    ∃ M : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K), Continuous M ∧
      (∀ y, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (M y) - r * M y = (c : InfiniteAdeleRing K) • y) ∧
      (∀ y, M (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) = (c : InfiniteAdeleRing K) • y) ∧
      Integrable (fun y : L ⊗[K] InfiniteAdeleRing K =>
        Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y))) * (((∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
            (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (y))‖ ^ 2)) : ℝ) : ℂ)) lam ∧
      Integrable (fun y : L ⊗[K] InfiniteAdeleRing K => Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y)))) lam ∧
      (∀ w' : NumberField.InfinitePlace L, Integrable (fun y : L ⊗[K] InfiniteAdeleRing K =>
        Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))) *
          (Real.log (‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖ ^ 2 +
            ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (M y))‖ ^ 2) : ℂ)) lam) ∧
      ((∏ v : NumberField.InfinitePlace K,
          ‖NumberField.AdelicLevel.archEval K v (c : InfiniteAdeleRing K)‖ ^ v.mult : ℝ) : ℂ) *
        ∫ y, Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y))) * (((∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
            (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (y))‖ ^ 2)) : ℝ) : ℂ) ∂lam =
      -2 * (Module.finrank K L : ℂ) *
          (((w.mult : ℝ) * Real.log ‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖ : ℝ) : ℂ) *
          ∫ y, Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))) ∂lam +
        ∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
          (w'.mult : ℂ) * ∫ y, Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))) *
            (Real.log (‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖ ^ 2 +
              ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (M y))‖ ^ 2) : ℂ) ∂lam := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_linearMap_prod_norm_pow_mul_integral_comp_sigmaTensor_sub_mul_twistedLogWeight_eq_add_sum.solution
