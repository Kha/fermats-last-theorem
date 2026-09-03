import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_prod_norm_one_sub_norm_pow_mult_mul_lintegral_comp_sigmaTensor_sub_mul_eq_lintegral

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.prod_norm_one_sub_norm_pow_mult_mul_lintegral_comp_sigmaTensor_sub_mul_eq_lintegral
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (lam' : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    (hreg : IsUnit (1 - Algebra.norm (InfiniteAdeleRing K) ((lam' : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K)))
    (G : (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞) (hG : Measurable G) :
    ENNReal.ofReal (∏ v : InfinitePlace K,
        ‖(1 - Algebra.norm (InfiniteAdeleRing K) ((lam' : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K)) v‖ ^
          v.mult) *
        ∫⁻ ξ, G (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ ξ - (lam' : L ⊗[K] InfiniteAdeleRing K) * ξ) ∂lam =
      ∫⁻ ξ, G ξ ∂lam := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_prod_norm_one_sub_norm_pow_mult_mul_lintegral_comp_sigmaTensor_sub_mul_eq_lintegral.solution
