import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import P2M.Util
import P2M.Sol.S_AutomorphicForm_map_mul_sigmaTensor_sub_mul_addHaar_infiniteAdeleRing_eq_inv_prod_norm_archEval_algebraNorm_sub_pow_mult_smul

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.map_mul_sigmaTensor_sub_mul_addHaar_infiniteAdeleRing_eq_inv_prod_norm_archEval_algebraNorm_sub_pow_mult_smul
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
        (((∏ w : NumberField.InfinitePlace K, ‖NumberField.AdelicLevel.archEval K w (Algebra.norm (InfiniteAdeleRing K) a - Algebra.norm (InfiniteAdeleRing K) b)‖ ^ w.mult)⁻¹ : ℝ) : ℂ) * ∫ y, g y ∂lam := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_map_mul_sigmaTensor_sub_mul_addHaar_infiniteAdeleRing_eq_inv_prod_norm_archEval_algebraNorm_sub_pow_mult_smul.solution
